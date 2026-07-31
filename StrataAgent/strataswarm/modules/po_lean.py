"""Python wrapper for SwarmAgentTools — persistent Lean RPC process.

Keeps a long-lived Lean process that handles file analysis commands.
Monitors memory usage and restarts when the process gets too bulky
(Lean's environment grows with each file it elaborates).

Inspired by itp-interface (https://github.com/trishullab/itp-interface)
which pioneered the Base64-RPC pattern for Lean tooling.

Usage:
    tools = SwarmLeanTools()
    result = tools.count_sorries("StrataAgent/Sandbox/decomposed/lemma_0.lean")
    # {"total": 3, "sorry_decls": ["helper_1", "main_thm", ...]}

    result = tools.list_theorems("StrataAgent/Sandbox/decomposed/lemma_2.lean")
    # {"theorems": [{"name": "X", "status": "sorry"}, ...]}

    tools.close()
"""

from __future__ import annotations

import base64
import json
import logging
import re
import os
import shutil
import signal
import subprocess
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

logger = logging.getLogger("strataswarm.lean_tools")

COMMAND_PAD = 15  # must match Lean side

# Soundness-adjacent source patterns invisible to `#print axioms` (a decl can be
# sorryAx-free yet compromised by `@[implemented_by]`, `opaque`, etc.). Ported
# verbatim from lean-lsp-mcp's verify.py so the oracle is a strict superset of
# lean_verify's `scan_source`. Advisory warnings — the LLM/guide decides risk.
_SOUNDNESS_WARNING_PATTERNS: list[str] = [
    r"set_option\s+debug\.",
    r"\bunsafe\b",
    r"@\[implemented_by\b",
    r"@\[extern\b",
    r"\bopaque\b",
    r"local\s+instance\b",
    r"local\s+notation\b",
    r"local\s+macro_rules\b",
    r"scoped\s+notation\b",
    r"scoped\s+instance\b",
    r"@\[csimp\b",
    r"import\s+Lean\.Elab\b",
    r"import\s+Lean\.Meta\b",
]


def _ascii_escape(name: str) -> str:
    """Escape a theorem name to a safe ASCII filename component.
    Keeps alphanumeric + underscore, replaces everything else with _."""
    return "".join(c if c.isalnum() or c == "_" else "_" for c in name)[:60]


def strip_comments(content: str) -> str:
    """Remove Lean comments, returning only code — a faithful Python port of
    ``LeanTools/Main.lean``'s ``stripComments``/``trimComment``.

    Handles NESTED block comments ``/- ... -/`` and line comments ``--``. This is
    needed before any syntactic dependency scan: a lemma name mentioned only
    inside a comment must NOT register as a real dependency edge. A naive
    ``str.replace``/single-level regex mishandles nesting; this mirrors the Lean
    depth-counting state machine exactly so the two implementations agree.

    Note: like the Lean original, this is a lexical stripper — it does not treat
    ``--``/``/-`` inside string literals specially. Lean proof bodies effectively
    never contain those tokens inside strings, and the Lean tool has shipped with
    the same limitation, so we preserve identical behavior rather than diverge.
    """
    out: list[str] = []
    i = 0
    n = len(content)
    depth = 0  # block-comment nesting depth; depth == 0 means "in code"
    while i < n:
        if depth == 0:
            if content.startswith("--", i):
                # Line comment: skip the comment text but PRESERVE the newline
                # (mirrors the Lean stripper, which keeps line structure). Unlike
                # the Lean original this also strips INLINE `--` comments, not just
                # line-leading ones — a trailing `-- uses foo_lemma` must not
                # register foo_lemma as a dependency edge.
                nl = content.find("\n", i)
                if nl == -1:
                    break
                out.append("\n")
                i = nl + 1
            elif content.startswith("/-", i):
                depth = 1
                i += 2
            else:
                out.append(content[i])
                i += 1
        else:
            if content.startswith("-/", i):
                depth -= 1
                i += 2
            elif content.startswith("/-", i):
                depth += 1
                i += 2
            else:
                i += 1
    return "".join(out)


def blank_comments(content: str) -> str:
    """Replace every comment character with a space, PRESERVING byte and line
    offsets exactly (newlines kept as-is, comment bytes overwritten with spaces).

    This is the position-preserving sibling of :func:`strip_comments`. Where
    ``strip_comments`` *deletes* comment text (collapsing line numbers — which
    silently shifts every subsequent line up), this keeps the file the same shape
    so a scan over the result reports the SAME line/column as the original source.

    It is the foundation of the single local-sorry source of truth
    (:func:`local_sorry_positions`): a text scan for the ``sorry`` token that must
    (a) ignore ``sorry`` appearing in comments/docstrings and (b) report the token
    at its true position. The Lean-side ``handleSorryPositions`` used the deleting
    stripper and therefore mislocated every sorry that sat below a block comment.

    Handles NESTED block comments ``/- ... -/`` and line comments ``--``, matching
    ``strip_comments``'s state machine. Like it, this is lexical — it does not treat
    ``--``/``/-`` inside string literals specially (Lean proof bodies effectively
    never contain those tokens inside strings).
    """
    out = list(content)
    i = 0
    n = len(content)
    depth = 0  # block-comment nesting depth; depth == 0 means "in code"
    while i < n:
        if depth == 0:
            if content.startswith("--", i):
                # Blank the line comment to end-of-line, keeping the newline.
                while i < n and content[i] != "\n":
                    out[i] = " "
                    i += 1
            elif content.startswith("/-", i):
                depth = 1
                out[i] = out[i + 1] = " "
                i += 2
            else:
                i += 1
        else:
            if content.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
            elif content.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
            else:
                # Blank comment interior but keep newlines so line numbers hold.
                if content[i] != "\n":
                    out[i] = " "
                i += 1
    return "".join(out)


# Word-boundary match for the bare `sorry` tactic/term token. Excludes identifiers
# like `sorryAx`, `my_sorry`, `sorry_free` — only the standalone keyword counts.
_SORRY_TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")


def local_sorry_positions(content: str) -> list[dict]:
    """THE single source of truth for LOCAL sorry detection in file text.

    Returns every real ``sorry`` token as ``{"line": int, "col": int}``, 0-indexed,
    comment-aware and position-accurate. Every other local-sorry query
    (count, has-sorry boolean, per-theorem grouping, per-block ``has_sorry``) is a
    thin view over this one function — so the counts, positions, and per-theorem
    breakdown can never contradict each other (the bug that made ``show_file_state``
    report a theorem "proved" while the file still had a ``sorry``).

    Why a text scan rather than compiler ``hasSorry`` diagnostics: the compiler
    emits NO ``hasSorry`` warning when elaboration aborts on a real error, so a
    file that is both broken AND has a sorry would read as sorry-free — exactly the
    mid-proof state the guide sees most. A comment-blanked token scan is robust to
    non-compiling files and also catches ``decreasing_by => sorry`` / positions the
    per-declaration diagnostic can't localize. Transitive sorry (through imports)
    is a DIFFERENT question, answered authoritatively by the axioms oracle.
    """
    code = blank_comments(content)
    positions: list[dict] = []
    for line_idx, line in enumerate(code.split("\n")):
        for m in _SORRY_TOKEN_RE.finditer(line):
            positions.append({"line": line_idx, "col": m.start()})
    return positions


# Lines that PREFIX a declaration but are not the declaration itself. The Lean
# parser lumps these into the following decl's block and can mis-name the block
# after them (e.g. `set_option warn.sorry false in` → block named `warn.sorry`).
_DECL_PREFIX_RE = re.compile(
    r"""^\s*(
          @\[[^\]]*\]            # attributes:  @[simp], @[inline], …
        | set_option\s+\S+\s+\S+\s+in\b   # set_option X v in
        | attribute\s+.*\bin\b            # attribute [..] name in
        | open\b.*\bin\b                  # open … in
        | public | private | protected | noncomputable | partial | unsafe | scoped | local
    )\s*""",
    re.VERBOSE,
)

# The actual declaration keyword + name once prefixes are stripped.
_DECL_HEAD_RE = re.compile(
    r"^\s*(theorem|lemma|def|instance|abbrev|example)\s+([^\s({\[:]+)")

# Any import statement, covering every Lean 4 module-system variant:
#   `import X`, `public import X`, `private import X`, `import all X`, `meta import X`
_IMPORT_LINE_RE = re.compile(r"^\s*(public\s+|private\s+|meta\s+)?import\b")


def _reconstruct_header(header_lines: list[str], extra_imports: list[str]) -> str:
    """Rebuild a helper file's preamble from the original file's VERBATIM header,
    inserting `extra_imports` (sibling `import …` lines) right after the last
    existing import.

    Preserving the header verbatim keeps the copyright comment, the `module`
    keyword, all import variants, the doc-comment, and the `namespace` / `open`
    / `section` preamble in their original order — which the Lean module system
    requires (`module` first, then imports, then everything else). Inserting the
    sibling imports after the last import keeps them inside the import section."""
    lines = list(header_lines)
    fresh = [imp for imp in extra_imports if imp not in lines]
    if not fresh:
        return "\n".join(lines)
    # Prefer inserting after the last existing import; otherwise after `module`;
    # otherwise at the very top (before any command).
    last_import = max((i for i, l in enumerate(lines) if _IMPORT_LINE_RE.match(l)),
                      default=None)
    if last_import is None:
        module_idx = next((i for i, l in enumerate(lines)
                           if l.strip() == "module" or l.strip().startswith("module ")), None)
        insert_at = (module_idx + 1) if module_idx is not None else 0
    else:
        insert_at = last_import + 1
    for offset, imp in enumerate(fresh):
        lines.insert(insert_at + offset, imp)
    return "\n".join(lines)


def _strip_decl_prefixes(text: str) -> str:
    """Drop leading doc-comments, attributes, and modifier-`in` lines so the
    real declaration head (`theorem foo …`) is first. Returns the remaining text."""
    lines = text.splitlines()
    i = 0
    in_block_comment = False
    while i < len(lines):
        stripped = lines[i].strip()
        if in_block_comment:
            if "-/" in stripped:
                in_block_comment = False
            i += 1
            continue
        if stripped == "" or stripped.startswith("--"):
            i += 1
            continue
        if stripped.startswith("/-"):
            if "-/" not in stripped:
                in_block_comment = True
            i += 1
            continue
        # Peel a single-line prefix (attribute / set_option … in / modifier).
        m = _DECL_PREFIX_RE.match(lines[i])
        if m:
            rest = lines[i][m.end():].strip()
            if rest:
                # prefix and decl share a line — keep the remainder in place
                lines[i] = rest
                break
            i += 1
            continue
        break
    return "\n".join(lines[i:]).lstrip()


def _real_decl_name(text: str) -> tuple[str | None, str | None]:
    """Given a declaration block's raw text (possibly with leading modifiers),
    return (name, kind) of the real declaration, or (None, None) if none is
    found. `kind` is normalized: lemma→theorem, everything else kept as-is."""
    head = _strip_decl_prefixes(text)
    m = _DECL_HEAD_RE.match(head)
    if not m:
        return None, None
    kind = m.group(1)
    if kind == "lemma":
        kind = "theorem"
    return m.group(2), kind


@dataclass
class AxiomCheckResult:
    has_axiom: bool = False
    axiom_names: list[str] = field(default_factory=list)
    error: str | None = None


@dataclass
class SourceWarning:
    """A soundness-adjacent source pattern that `#print axioms` cannot see
    (e.g. `@[implemented_by]`, `opaque`, `unsafe`). Advisory, not a hard gate —
    matches lean_verify's `scan_source` warnings."""
    line: int
    pattern: str


@dataclass
class AxiomSorryResult:
    """Per-theorem transitive-sorry verdict from `#print axioms`.

    This is produced by the build-then-probe oracle (see
    ``SwarmLeanTools.axioms_by_theorem``): the target module is built to a fresh
    olean, then a throwaway NON-module scratch file imports it and runs
    ``#print axioms <name>``. Reading the built olean is what makes the axiom set
    TRANSITIVE (it sees sorry reached through imported helpers), and doing it from
    a non-module file is what makes it work at all on this repo's ``module`` files
    (``#print axioms`` is illegal inside a ``module``).

    sorry_by_name[name] is True iff the theorem transitively depends on `sorryAx`.
    ok_by_name[name] is True iff a parseable `#print axioms` verdict was produced
    for it (False means the name wasn't found / elaboration failed — treat as NOT
    confirmed, never as proven).
    axioms_by_name[name] is the full transitive axiom list (parity with
    lean_verify's `axioms`), e.g. ``["propext", "Classical.choice", "Quot.sound"]``.
    build_ok is False iff `lake build <module>` failed (real compile error) — in
    that case NO name is confirmed (we couldn't check), which is distinct from a
    genuine "depends on sorry" verdict.
    warnings mirrors lean_verify's source-pattern scan."""
    sorry_by_name: dict[str, bool] = field(default_factory=dict)
    ok_by_name: dict[str, bool] = field(default_factory=dict)
    axioms_by_name: dict[str, list[str]] = field(default_factory=dict)
    warnings: list[SourceWarning] = field(default_factory=list)
    build_ok: bool = True
    build_error: str | None = None
    error: str | None = None

    def is_proven(self, name: str) -> bool:
        """True only if the build succeeded, we got a verdict, AND it depends on
        no sorry. Build failure and 'name not found' both return False — we never
        conflate 'couldn't check' with 'proven'."""
        return (
            self.build_ok
            and self.ok_by_name.get(name, False)
            and not self.sorry_by_name.get(name, True)
        )


def _get_project_root() -> Path:
    """Walk up from this file to find lakefile.toml."""
    p = Path(__file__).resolve()
    while p != p.parent:
        if (p / "lakefile.toml").exists():
            return p
        p = p.parent
    return Path.cwd()


def _get_exe_path() -> Path:
    root = _get_project_root()
    return root / ".lake" / "build" / "bin" / "SwarmAgentTools"


def _get_process_rss_kb(pid: int) -> int:
    """Get RSS (resident set size) in kB for a process."""
    try:
        with open(f"/proc/{pid}/status", "r") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
    except (FileNotFoundError, ValueError, PermissionError):
        pass
    return 0


# ─── Result types ────────────────────────────────────────────────────────────

@dataclass
class SorryInfo:
    total: int = 0
    sorry_decls: list[str] = field(default_factory=list)
    error: str | None = None


@dataclass
class TheoremInfo:
    name: str = ""
    status: str = ""  # "sorry" | "proved"


@dataclass
class TheoremsResult:
    theorems: list[TheoremInfo] = field(default_factory=list)
    error: str | None = None


@dataclass
class ImportsResult:
    imports: list[str] = field(default_factory=list)
    error: str | None = None


@dataclass
class CompileResult:
    success: bool = False
    has_sorry: bool = False
    has_error: bool = False
    error: str | None = None


@dataclass
class TheoremBlock:
    name: str = ""
    start: int = 0  # line number (1-indexed, from itp_interface)
    end: int = 0
    has_sorry: bool = False
    decl_type: str = ""  # "theorem", "def", "unknown", "end"
    text: str = ""  # full declaration text (clean, no trailing comments)
    mutual_group: int | None = None  # index of mutual group, or None


@dataclass
class SplitResult:
    blocks: list[TheoremBlock] = field(default_factory=list)
    mutual_groups: dict[int, list[str]] = field(default_factory=dict)
    error: str | None = None


@dataclass
class DeclSorryInfo:
    """Per-declaration sorry status for the guide's authoritative overview."""
    name: str = ""
    start: int = 0                       # 1-indexed decl start line (0 if unknown)
    end: int = 0
    has_local_sorry: bool = False        # literal `sorry` token in this block
    has_transitive_sorry: bool = True    # reaches sorryAx (authoritative, module-safe)
    sorry_positions: list[dict] = field(default_factory=list)  # [{line,col},...]


@dataclass
class TargetSorryInfo:
    """Per-target roll-up: is it done, and which reachable decls are still open."""
    name: str = ""
    done: bool = False                   # build-ok AND transitively sorry-free
    open_deps: list[str] = field(default_factory=list)   # reachable decls w/ sorry
    reachable: list[str] = field(default_factory=list)   # all in-file reachable decls


@dataclass
class TransitiveSorryMap:
    """Joined dependency + sorry overview across a set of target theorems."""
    file_path: str = ""
    build_ok: bool = True
    build_error: str | None = None
    error: str | None = None
    decls: dict[str, DeclSorryInfo] = field(default_factory=dict)
    targets: dict[str, TargetSorryInfo] = field(default_factory=dict)

    def open_sorry_count(self) -> int:
        """Total DISTINCT in-file decls (across all targets) still transitively
        carrying a sorry — the guide's progress metric (replaces protected-only)."""
        return sum(1 for d in self.decls.values() if d.has_transitive_sorry)


@dataclass
class ExtractResult:
    created_files: list[str] = field(default_factory=list)
    extracted_names: list[str] = field(default_factory=list)
    original_updated: str = ""
    skipped: bool = False
    reason: str = ""
    error: str | None = None


@dataclass
class MoveIntent:
    """A registered intent to move a declaration to its own file."""
    decl_name: str
    additional_imports: list[str] = field(default_factory=list)  # names of other decls this depends on


class MoveSession:
    """Accumulates move_decl intents, commits them, supports revert/finalize.

    Lifecycle:
        session = MoveSession(tools, file_path, main_theorem, workspace)
        session.get_declarations()  # LLM sees what's available
        session.move_decl("helper_a", additional_imports=["helper_b"])
        session.move_decl("helper_b", additional_imports=[])
        result = session.commit()   # writes files, rewrites Stub.lean, builds
        if result.error:
            session.revert()        # undo everything, back to original
            # try again...
        else:
            session.finalize()      # remove backup, extraction complete
    """

    def __init__(self, tools: "SwarmLeanTools", file_path: str, main_theorem: str, workspace: str,
                 output_subdir: str = "decomposed"):
        self._tools = tools
        self._file_path = file_path
        self._main_theorem = main_theorem
        self._workspace = workspace
        self._output_subdir = output_subdir
        self._moves: list[MoveIntent] = []
        self._split: SplitResult | None = None
        self._backup: str | None = None  # original file content
        self._committed = False
        self._move_stack: list[tuple[str, str]] = []  # [(name, stub_content_before_move), ...]

    def get_declarations(self) -> list[dict]:
        """Return declaration info for the LLM to see. Also takes backup."""
        root = self._tools._root
        source = root / self._file_path
        if self._backup is None:
            self._backup = source.read_text()
        self._split = self._tools.split_theorems(self._file_path)
        if self._split.error:
            return []
        return [
            {
                "name": b.name,
                "decl_type": b.decl_type,
                "has_sorry": b.has_sorry,
                "lines": f"{b.start}-{b.end}",
                "mutual_group": b.mutual_group,
                "is_main": b.name == self._main_theorem,
            }
            for b in self._split.blocks
        ]

    def move_decl(self, decl_name: str, additional_imports: list[str] | None = None) -> str:
        """Register intent to move a declaration. Returns confirmation or error."""
        if not self._split:
            self._split = self._tools.split_theorems(self._file_path)

        # Validate decl exists
        block = next((b for b in self._split.blocks if b.name == decl_name), None)
        if not block:
            return f"Error: declaration '{decl_name}' not found in file"
        if decl_name == self._main_theorem:
            return f"Error: cannot move main theorem '{decl_name}'"

        # If part of a mutual group, all members must be moved together
        if block.mutual_group is not None:
            group_names = self._split.mutual_groups.get(block.mutual_group, [])
            # If the main theorem is in this mutual group, NONE of them can be moved
            if self._main_theorem in group_names:
                return f"Error: cannot move '{decl_name}' — it is in a mutual block with main theorem '{self._main_theorem}'"
            # Check if any group member is already registered
            already = [m for m in self._moves if m.decl_name in group_names]
            if already:
                return f"OK: '{decl_name}' is in mutual group with {group_names}, already registered via '{already[0].decl_name}'"
            # Register all members as one move (use first name)
            self._moves.append(MoveIntent(
                decl_name=group_names[0],
                additional_imports=additional_imports or [],
            ))
            return f"OK: moved mutual group {group_names} (filed under '{group_names[0]}')"

        # Check not already moved
        if any(m.decl_name == decl_name for m in self._moves):
            return f"OK: '{decl_name}' already registered"

        self._moves.append(MoveIntent(
            decl_name=decl_name,
            additional_imports=additional_imports or [],
        ))
        return f"OK: registered move for '{decl_name}'"

    def commit(self) -> ExtractResult:
        """Atomically extract all registered declarations into separate files.

        This is the ONLY method that mutates files. It:
        1. Re-parses Stub.lean fresh (ignoring any prior move_lines state)
        2. For each registered move_decl, extracts the declaration text
        3. Writes each helper file with ONLY its needed imports (not all of them)
        4. Rewrites Stub.lean: removes extracted blocks, adds imports
        5. Verifies everything compiles

        All-or-nothing: if any step fails, revert() can restore the original.
        """
        import subprocess

        root = self._tools._root
        source = root / self._file_path
        out_path = root / self._workspace / self._output_subdir

        if not self._moves:
            return ExtractResult(error="No declarations registered for extraction")

        # Take backup if not already done
        if self._backup is None:
            self._backup = source.read_text()

        # Re-parse fresh from the ORIGINAL file (not any modified state)
        source.write_text(self._backup)
        split = self._tools.split_theorems(self._file_path)
        if not split or split.error:
            return ExtractResult(error=f"Cannot parse file: {split.error if split else 'unknown'}")

        # Build block lookup
        block_by_name = {b.name: b for b in split.blocks}

        # Determine the stable header: EVERYTHING before the first declaration
        # block. Real Strata files open with a `/-` copyright comment, then
        # `module`, imports (incl. `public import` / `import all`), a doc-comment,
        # then `namespace` / `open` / `section`. A per-line keyword allowlist that
        # `break`s on the first non-matching line fails immediately on line 1
        # (`/-`), stripping the whole preamble. Instead, take the header as all
        # lines before the earliest block start (1-indexed) so the copyright,
        # `module`, imports, `open`, and `namespace` are all preserved verbatim.
        original_lines = self._backup.splitlines()
        first_block_start = min((b.start for b in split.blocks), default=len(original_lines) + 1)
        header_lines = original_lines[:first_block_start - 1]  # start is 1-indexed
        base_header = "\n".join(header_lines)

        # Resolve which blocks to extract
        blocks_to_extract: list[tuple[str, list["TheoremBlock"]]] = []  # (safe_name, blocks)
        names_being_extracted: set[str] = set()

        for move in self._moves:
            block = block_by_name.get(move.decl_name)
            if not block:
                continue

            # If mutual group, extract all members together
            if block.mutual_group is not None:
                group_names = split.mutual_groups.get(block.mutual_group, [move.decl_name])
                group_blocks = [block_by_name[n] for n in group_names if n in block_by_name]
                safe_name = move.decl_name
                blocks_to_extract.append((safe_name, group_blocks))
                names_being_extracted.update(group_names)
            else:
                blocks_to_extract.append((move.decl_name, [block]))
                names_being_extracted.add(move.decl_name)

        if not blocks_to_extract:
            return ExtractResult(error="No valid declarations found to extract")

        # Create output directory
        out_path.mkdir(parents=True, exist_ok=True)

        # Write each helper file. The preamble is the ORIGINAL header verbatim
        # (copyright, `module`, imports, doc-comment, `namespace`, `open`,
        # `section`), with sibling imports from the agent's explicit
        # additional_imports inserted into the import section. The agent decides
        # dependencies via move_decl(additional_imports=[...]); no heuristic
        # auto-extraction or string-match dependency inference.
        created_files: list[str] = []
        for safe_name, blocks in blocks_to_extract:
            fs_name = safe_name.replace(" ", "_").replace("/", "_")
            target_file = out_path / f"lemma_helper_{fs_name}.lean"

            # Sibling imports from agent's explicit additional_imports
            extra_imports: list[str] = []
            move_intent = next((m for m in self._moves if m.decl_name == safe_name), None)
            if move_intent and move_intent.additional_imports:
                for ai in move_intent.additional_imports:
                    ai_fs = ai.replace(" ", "_").replace("/", "_")
                    module = f"{self._workspace}.{self._output_subdir}.lemma_helper_{ai_fs}".replace("/", ".")
                    imp_line = f"import {module}"
                    if imp_line not in extra_imports:
                        extra_imports.append(imp_line)

            # Preserve the full preamble verbatim; splice sibling imports in.
            header_text = _reconstruct_header(header_lines, extra_imports)

            # Build file content
            blocks_text = "\n\n".join(b.text for b in blocks)
            file_content = f"{header_text}\n\n{blocks_text}\n"
            target_file.write_text(file_content)
            created_files.append(str(target_file.relative_to(root)))

        # Rewrite Stub.lean: remove extracted blocks, add imports for them
        # Determine which line ranges to remove
        lines_to_remove: set[int] = set()  # 0-indexed
        for _, blocks in blocks_to_extract:
            for block in blocks:
                for i in range(block.start - 1, block.end):  # start/end are 1-indexed
                    lines_to_remove.add(i)

        # Build new Stub.lean
        new_lines = []
        # First: add all existing imports (any variant: `public import`,
        # `import all`, plain `import`), keeping everything up to and including
        # the last import line — which also preserves the `module` keyword and
        # copyright comment that precede the imports.
        import_section_end = 0
        for i, l in enumerate(original_lines):
            if _IMPORT_LINE_RE.match(l):
                import_section_end = i + 1

        # Copy original imports
        for i in range(import_section_end):
            new_lines.append(original_lines[i])

        # Add new imports for extracted helpers
        for safe_name, _ in blocks_to_extract:
            fs_name = safe_name.replace(" ", "_").replace("/", "_")
            module = f"{self._workspace}.{self._output_subdir}.lemma_helper_{fs_name}".replace("/", ".")
            imp_line = f"import {module}"
            if imp_line not in new_lines:
                new_lines.append(imp_line)

        # Copy remaining lines, skipping extracted blocks
        for i in range(import_section_end, len(original_lines)):
            if i not in lines_to_remove:
                new_lines.append(original_lines[i])

        # Clean up multiple blank lines
        cleaned = []
        prev_blank = False
        for l in new_lines:
            if l.strip() == "":
                if not prev_blank:
                    cleaned.append(l)
                prev_blank = True
            else:
                cleaned.append(l)
                prev_blank = False

        source.write_text("\n".join(cleaned))

        # Verify: build Stub.lean (which transitively builds all imported helpers)
        stub_module = self._file_path.replace("/", ".").removesuffix(".lean")
        result = subprocess.run(["lake", "build", stub_module],
                                cwd=str(root), capture_output=True, text=True, timeout=300)
        output = result.stdout + "\n" + result.stderr
        errors = [l for l in output.splitlines()
                  if ": error:" in l or l.strip().startswith("error:")]

        if errors:
            # Categorize errors by file
            error_summary = "\n".join(errors[:10])
            return ExtractResult(
                error=f"Build failed after extraction:\n{error_summary}",
                created_files=created_files)

        self._committed = True
        self._created_files = created_files
        self._extracted_names = [n for n, _ in blocks_to_extract]

        return ExtractResult(created_files=created_files, extracted_names=self._extracted_names)

    def revert(self) -> str:
        """Undo everything: restore original Stub.lean, remove decomposed files."""
        root = self._tools._root
        source = root / self._file_path

        if self._backup is None:
            return "Error: no backup available (get_declarations not called?)"

        # Restore original file
        source.write_text(self._backup)

        # Remove decomposed files we created
        out_path = root / self._workspace / self._output_subdir
        if out_path.exists():
            shutil.rmtree(out_path)

        # Reset state for retry
        self._moves.clear()
        self._move_stack.clear()
        self._committed = False
        self._split = None

        return "OK: reverted to original"

    def move_lines(self, start: int, end: int, name: str) -> str:
        """Move lines start-end (1-indexed, inclusive) from Stub.lean into lemma_helper_<name>.lean.

        Creates the file if it doesn't exist (with header from Stub.lean), or appends.
        Removes those lines from Stub.lean and adds an import.
        Snapshots Stub.lean before modifying (for revert_move).
        """
        root = self._tools._root
        source = root / self._file_path
        if self._backup is None:
            self._backup = source.read_text()

        # Save state before this move (for revert_last)
        safe_name = name.replace(" ", "_").replace("/", "_")
        self._move_stack.append((safe_name, source.read_text()))

        lines = source.read_text().splitlines()
        if start < 1 or end > len(lines) or start > end:
            return f"Error: invalid range {start}-{end} (file has {len(lines)} lines)"

        # Extract the block (1-indexed → 0-indexed)
        block_lines = lines[start - 1:end]
        block_text = "\n".join(block_lines)

        # Determine output path
        out_path = root / self._workspace / self._output_subdir
        out_path.mkdir(parents=True, exist_ok=True)
        safe_name = name.replace(" ", "_").replace("/", "_")
        target_file = out_path / f"lemma_helper_{safe_name}.lean"

        if target_file.exists():
            # Append to existing file
            existing = target_file.read_text()
            target_file.write_text(existing.rstrip() + "\n\n" + block_text + "\n")
        else:
            # Create with header = everything before the first declaration block
            # of Stub.lean. Parse to find the earliest block start so the full
            # preamble (copyright comment, `module`, all import variants, `open`,
            # `namespace`, `section`) is carried over verbatim — a per-line
            # keyword allowlist `break`s on the leading `/-` copyright comment and
            # loses the whole header.
            split = self._tools.split_theorems(self._file_path)
            if split and split.blocks and not split.error:
                first_block_start = min(b.start for b in split.blocks)
                header_lines = lines[:first_block_start - 1]  # start is 1-indexed
            else:
                # Fallback: keep everything up to and including the last import.
                last_import = max((i for i, l in enumerate(lines) if _IMPORT_LINE_RE.match(l)),
                                  default=-1)
                header_lines = lines[:last_import + 1]
            header = "\n".join(header_lines)
            target_file.write_text(header + "\n\n" + block_text + "\n")

        # Remove lines from source and add import
        remaining = lines[:start - 1] + lines[end:]
        module_path = f"{self._workspace}.{self._output_subdir}.lemma_helper_{safe_name}".replace("/", ".")
        import_line = f"import {module_path}"

        # Add import if not already present
        if import_line not in "\n".join(remaining):
            # Insert after last existing import
            insert_pos = 0
            for i, l in enumerate(remaining):
                if l.strip().startswith("import "):
                    insert_pos = i + 1
            remaining.insert(insert_pos, import_line)

        source.write_text("\n".join(remaining))
        rel_target = str(target_file.relative_to(root))
        return f"OK: moved lines {start}-{end} to {rel_target}"

    def add_imports(self, imports: list[str], name: str) -> str:
        """Add import statements to lemma_helper_<name>.lean.

        Each entry in imports should be a full module path (e.g. 'StrataAgent.Sandbox.Stub.Def')
        or a helper name (e.g. 'detBlockSim' → resolved to the decomposed module path).
        """
        root = self._tools._root
        out_path = root / self._workspace / self._output_subdir
        safe_name = name.replace(" ", "_").replace("/", "_")
        target_file = out_path / f"lemma_helper_{safe_name}.lean"

        if not target_file.exists():
            return f"Error: lemma_helper_{safe_name}.lean does not exist"

        content = target_file.read_text()
        lines = content.splitlines()

        added = []
        for imp in imports:
            # If it's a short name, resolve to decomposed module path
            if "." not in imp:
                imp_safe = imp.replace(" ", "_").replace("/", "_")
                module_path = f"{self._workspace}.{self._output_subdir}.lemma_helper_{imp_safe}".replace("/", ".")
            else:
                module_path = imp

            import_line = f"import {module_path}"
            if import_line not in [l.strip() for l in lines]:
                # Insert after last import
                insert_pos = 0
                for i, l in enumerate(lines):
                    if l.strip().startswith("import "):
                        insert_pos = i + 1
                lines.insert(insert_pos, import_line)
                added.append(module_path)

        if added:
            target_file.write_text("\n".join(lines))
            return f"OK: added {len(added)} imports to lemma_helper_{safe_name}.lean: {added}"
        return f"OK: all imports already present in lemma_helper_{safe_name}.lean"

    def add_import_to_helper(self, helper_name: str, module_path: str,
                             ancestor_modules: list[str] | None = None) -> str:
        """Safely add an import to a just-extracted helper file and verify it builds.

        Additive-only repair: adds a single `import <module_path>` line to
        lemma_helper_<helper_name>.lean, then rebuilds that helper's module. If
        the build fails, the change is reverted. Refuses imports that would form
        a cycle in the proof DAG (an ancestor's `Stub`). Declaration bodies are
        never touched, so this cannot smuggle in `sorry`/`axiom`.

        Returns a human-readable OK/BLOCKED/FAILED message (tool-facing)."""
        import subprocess

        root = self._tools._root
        out_path = root / self._workspace / self._output_subdir
        safe_name = helper_name.replace(" ", "_").replace("/", "_")
        target_file = out_path / f"lemma_helper_{safe_name}.lean"
        if not target_file.exists():
            return f"Error: lemma_helper_{safe_name}.lean does not exist (extract it first)"

        # Resolve a bare helper name to its decomposed module path.
        if "." not in module_path:
            mp_safe = module_path.replace(" ", "_").replace("/", "_")
            module_path = f"{self._workspace}.{self._output_subdir}.lemma_helper_{mp_safe}".replace("/", ".")

        # Cycle check: importing an ancestor's Stub would close a loop in the DAG.
        circular = {f"{anc}.Stub" for anc in (ancestor_modules or [])}
        if module_path in circular:
            return (f"BLOCKED: '{module_path}' is an ancestor's Stub in the proof DAG. "
                    f"Importing it would create a circular dependency.")

        import_line = f"import {module_path}"
        original = target_file.read_text()
        lines = original.splitlines()
        if import_line in [l.strip() for l in lines]:
            return f"OK: already imported ({module_path})"

        # Insert after the last existing import (module-first ordering preserved).
        new_content = _reconstruct_header(lines, [import_line])
        target_file.write_text(new_content + ("\n" if not new_content.endswith("\n") else ""))

        # Verify the helper module builds; revert on failure.
        helper_module = f"{self._workspace}.{self._output_subdir}.lemma_helper_{safe_name}".replace("/", ".")
        result = subprocess.run(["lake", "build", helper_module],
                                cwd=str(root), capture_output=True, text=True, timeout=300)
        output = result.stdout + "\n" + result.stderr
        errors = [l for l in output.splitlines()
                  if ": error:" in l or l.strip().startswith("error:")]
        if errors:
            target_file.write_text(original)
            return (f"FAILED: adding '{import_line}' breaks the build. Reverted.\n"
                    + "\n".join(errors[:8]))
        return f"OK: added '{import_line}' — lemma_helper_{safe_name}.lean compiles."

    def revert_last(self) -> str:
        """Undo the last move_lines: restore Stub.lean and delete the extracted file."""
        if not self._move_stack:
            return "Error: nothing to revert (no moves on stack)"

        root = self._tools._root
        out_path = root / self._workspace / self._output_subdir
        safe_name, prev_content = self._move_stack.pop()

        # Restore Stub.lean to state before that move
        source = root / self._file_path
        source.write_text(prev_content)

        # Delete the extracted file
        target_file = out_path / f"lemma_helper_{safe_name}.lean"
        if target_file.exists():
            target_file.unlink()

        return f"OK: reverted last move (lemma_helper_{safe_name}), Stub.lean restored"

    def compile_check(self, name: str) -> str:
        """Check if lemma_helper_<name>.lean compiles. Returns errors or 'OK'."""
        root = self._tools._root
        out_path = root / self._workspace / self._output_subdir
        safe_name = name.replace(" ", "_").replace("/", "_")
        target_file = out_path / f"lemma_helper_{safe_name}.lean"

        if not target_file.exists():
            return f"Error: lemma_helper_{safe_name}.lean does not exist"

        rel_path = str(target_file.relative_to(root))
        cr = self._tools.check_compiles(rel_path)
        if cr.success:
            return f"OK: compiles{' (has sorry)' if cr.has_sorry else ' (sorry-free)'}"
        else:
            return f"ERRORS:\n{cr.error or 'unknown compilation error'}"

    def finalize(self) -> str:
        """Confirm extraction is done. Remove backup, extraction is permanent."""
        if not self._committed:
            return "Error: nothing committed yet"

        # Verify one last time
        cr = self._tools.check_compiles(self._file_path)
        has_sorry = self._tools.has_sorry(self._file_path)
        if not cr.success:
            return "Error: Stub.lean doesn't compile — cannot finalize"
        if has_sorry:
            return "Error: Stub.lean still has sorry — cannot finalize"

        # Clear backup (extraction is permanent)
        self._backup = None
        return "OK: finalized"


@dataclass
class WriteResult:
    file_path: str = ""
    theorem_name: str = ""
    has_sorry: bool = True
    error: str | None = None


# ─── Main wrapper class ──────────────────────────────────────────────────────

class SwarmLeanTools:
    """Persistent Lean RPC process for file analysis.

    Keeps the process alive across calls. Monitors memory and restarts
    when RSS exceeds the limit (Lean grows as it elaborates files).
    """

    def __init__(
        self,
        project_root: str | Path | None = None,
        memory_limit_mb: int = 2048,
        restart_after_calls: int = 100,
    ):
        self._root = Path(project_root) if project_root else _get_project_root()
        self._exe = _get_exe_path()
        self._memory_limit_kb = memory_limit_mb * 1024
        self._restart_after = restart_after_calls
        self._call_count = 0
        self._process: subprocess.Popen | None = None
        self._lock = threading.Lock()
        self._start()

    def _start(self):
        """Start or restart the Lean process."""
        self._kill()
        if not self._exe.exists():
            raise FileNotFoundError(
                f"SwarmAgentTools not built. Run: cd {self._root} && lake build SwarmAgentTools"
            )

        self._process = subprocess.Popen(
            [str(self._exe)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
            cwd=str(self._root),
        )
        self._call_count = 0

        # Read the ready signal
        ready_line = self._process.stdout.readline().strip()
        if not ready_line:
            raise RuntimeError("SwarmAgentTools process failed to start")

        try:
            ready = json.loads(ready_line)
            if ready.get("status") != "ready":
                raise RuntimeError(f"Unexpected startup response: {ready_line}")
        except json.JSONDecodeError:
            raise RuntimeError(f"Invalid startup response: {ready_line}")

        logger.debug(f"SwarmAgentTools started (PID: {self._process.pid})")

    def _kill(self):
        """Kill the process if running."""
        if self._process and self._process.poll() is None:
            try:
                self._process.stdin.write("exit\n")
                self._process.stdin.flush()
                self._process.wait(timeout=2)
            except Exception:
                try:
                    self._process.kill()
                except Exception:
                    pass
        self._process = None

    def _ensure_running(self):
        """Restart if dead or too bulky."""
        if self._process is None or self._process.poll() is not None:
            logger.info("SwarmAgentTools process died, restarting...")
            self._start()
            return

        # Check memory
        rss_kb = _get_process_rss_kb(self._process.pid)
        if rss_kb > self._memory_limit_kb:
            logger.info(
                f"SwarmAgentTools RSS={rss_kb // 1024}MB > limit={self._memory_limit_kb // 1024}MB, restarting..."
            )
            self._start()
            return

        # Check call count
        if self._call_count >= self._restart_after:
            logger.debug(f"SwarmAgentTools reached {self._call_count} calls, restarting for freshness...")
            self._start()

    def _send(self, command: str, payload: str) -> dict:
        """Send a command and return parsed JSON response."""
        with self._lock:
            self._ensure_running()
            self._call_count += 1

            # Encode payload as base64
            b64 = base64.b64encode(payload.encode("utf-8")).decode("ascii")

            # Command is exactly COMMAND_PAD chars — no padding needed
            assert len(command) == COMMAND_PAD, f"Command must be {COMMAND_PAD} chars, got {len(command)!r}"
            line = f"{command}{b64}\n"

            try:
                self._process.stdin.write(line)
                self._process.stdin.flush()

                response_line = self._process.stdout.readline()
                if not response_line:
                    # Process died
                    self._start()
                    return {"error": "process died, restarted"}

                return json.loads(response_line.strip())
            except (BrokenPipeError, OSError) as e:
                logger.warning(f"Pipe error: {e}, restarting...")
                self._start()
                return {"error": str(e)}
            except json.JSONDecodeError as e:
                return {"error": f"invalid JSON: {e}", "raw": response_line.strip()[:200]}

    # ─── Public API ──────────────────────────────────────────────────────

    def _read_source(self, file_path: str) -> str | None:
        """Read a repo-relative (or absolute) Lean source file. None on failure."""
        try:
            p = Path(file_path)
            if not p.is_absolute():
                p = self._root / file_path
            return p.read_text(encoding="utf-8")
        except OSError:
            return None

    def _local_sorry_report(self, file_path: str) -> dict:
        """THE single per-file local-sorry computation. All local-sorry queries
        (count_sorries, get_sorry_positions, get_sorries_by_theorem, has_sorry)
        are thin views over this — so their answers can never disagree.

        Reads the file once, finds every real `sorry` token via the comment-aware
        position-preserving :func:`local_sorry_positions`, then groups those
        positions into declaration blocks from :meth:`split_theorems`.

        Returns a dict:
            positions:  [{"line","col"}, ...]   0-indexed, whole file
            total:      int                     count of real sorry tokens
            by_theorem: {name: [positions]}     positions grouped by decl block
            sorry_decls:[name, ...]             decls carrying >=1 sorry
            error:      str | None              set if the source can't be read
        """
        content = self._read_source(file_path)
        if content is None:
            return {"positions": [], "total": 0, "by_theorem": {},
                    "sorry_decls": [], "error": f"cannot read {file_path}"}

        positions = local_sorry_positions(content)

        # Group into declaration blocks. split_theorems is the source of RANGES;
        # positions are 0-indexed, block.start/end are 1-indexed.
        by_theorem: dict[str, list[dict]] = {}
        split = self.split_theorems(file_path)
        if not split.error:
            for block in split.blocks:
                block_sorries = [
                    pos for pos in positions
                    if block.start <= pos["line"] + 1 <= block.end
                ]
                if block_sorries:
                    by_theorem[block.name] = block_sorries

        return {
            "positions": positions,
            "total": len(positions),
            "by_theorem": by_theorem,
            "sorry_decls": list(by_theorem.keys()),
            "error": None,
        }

    def count_sorries(self, file_path: str) -> SorryInfo:
        """Count sorries in a file. Returns per-declaration breakdown.

        View over :meth:`_local_sorry_report` (the single local-sorry source) —
        a comment-aware token scan, NOT the old text/RPC count that mis-counted
        `sorry` appearing in doc-comments and compiler echoes.
        """
        report = self._local_sorry_report(file_path)
        if report["error"]:
            return SorryInfo(error=report["error"])
        return SorryInfo(
            total=report["total"],
            sorry_decls=report["sorry_decls"],
        )

    def list_theorems(self, file_path: str) -> TheoremsResult:
        """List all theorems with sorry/proved status."""
        result = self._send("list__theorems_", file_path)
        if "error" in result:
            return TheoremsResult(error=result["error"])
        return TheoremsResult(
            theorems=[TheoremInfo(name=t["name"], status=t["status"])
                      for t in result.get("theorems", [])],
        )

    def check_imports(self, file_path: str) -> ImportsResult:
        """Get all import statements from a file."""
        result = self._send("check__imports_", file_path)
        if "error" in result:
            return ImportsResult(error=result["error"])
        return ImportsResult(imports=result.get("imports", []))

    def check_compiles(self, file_path: str) -> CompileResult:
        """Check if a file compiles. Uses lake build + return code.

        Returns CompileResult with error details in the `error` field when compilation fails.
        """
        import subprocess
        try:
            module_name = file_path.replace("/", ".").removesuffix(".lean")
            result = subprocess.run(
                ["lake", "build", module_name],
                cwd=str(self._root),
                capture_output=True,
                text=True,
                timeout=120,
            )
            output = result.stdout + "\n" + result.stderr
            # The sorry diagnostic is EXACTLY "declaration uses 'sorry'" (emitted as a
            # warning, or as an `error:` line when the project sets warningAsError=true).
            # It is the ONLY signal for has_sorry — a bare "sorry" substring would also
            # match comments, identifiers, and file paths.
            has_sorry = "declaration uses 'sorry'" in output

            if result.returncode == 0:
                return CompileResult(success=True, has_sorry=has_sorry, has_error=False)

            # Non-zero return code — separate the benign sorry diagnostic from real errors.
            # Match the specific sorry diagnostic, NOT a bare "sorry" substring: a genuine
            # error line that merely mentions a sorry-named identifier must NOT be swallowed.
            def _is_sorry_diag(line: str) -> bool:
                return "declaration uses 'sorry'" in line

            error_lines = [l for l in output.splitlines()
                           if ("error" in l.lower() or "unknown" in l.lower()
                               or "failed" in l.lower())
                           and not _is_sorry_diag(l)]
            # No REAL error lines left after excluding the sorry diagnostic → it compiles
            # (with sorry, if present). This is the warningAsError=true case: the only
            # `error:` line was "declaration uses 'sorry'".
            if not error_lines:
                return CompileResult(success=True, has_sorry=has_sorry, has_error=False)

            error_detail = "\n".join(error_lines[:10])
            return CompileResult(success=False, has_sorry=has_sorry, has_error=True, error=error_detail)
        except subprocess.TimeoutExpired:
            return CompileResult(error="compilation timed out (120s)")
        except Exception as e:
            return CompileResult(error=str(e))

    def check_axioms(self, file_path: str) -> AxiomCheckResult:
        """Check if a file contains axiom declarations (unsound).
        Uses comment stripping — not fooled by axiom in comments/strings."""
        result = self._send("check___axioms_", file_path)
        if "error" in result:
            return AxiomCheckResult(error=result["error"])
        return AxiomCheckResult(
            has_axiom=result.get("has_axiom", False),
            axiom_names=result.get("axiom_names", []),
        )

    def _scan_source_warnings(self, file_path: str) -> list[SourceWarning]:
        """Grep the source for soundness-adjacent patterns invisible to
        `#print axioms` (parity with lean_verify's scan_source). Best-effort:
        returns [] on any read failure."""
        warnings: list[SourceWarning] = []
        try:
            text = (self._root / file_path).read_text(encoding="utf-8")
        except Exception:
            return warnings
        for lineno, line in enumerate(text.splitlines(), start=1):
            for pat in _SOUNDNESS_WARNING_PATTERNS:
                if m := re.search(pat, line):
                    warnings.append(SourceWarning(line=lineno, pattern=m.group(0)))
                    break
        return warnings

    def axioms_by_theorem(self, file_path: str, names: list[str]) -> AxiomSorryResult:
        """Transitive sorry check via `#print axioms` — the AUTHORITATIVE proof oracle.

        A theorem is genuinely proven iff it transitively depends on NO `sorryAx`.
        Unlike text-based has_sorry (which only sees literal `sorry` tokens), this
        catches sorry reached through imported helpers or referenced lemmas.

        Correctness-first design (replaces the old in-place `print_axioms___` RPC,
        which was broken on `module` files because `#print axioms` is illegal inside
        a `module`):

          1. `lake build <module>` the target FIRST → guarantees a fresh olean, so
             we never read a stale cache (the classic false-success trap). If the
             build fails, we return build_ok=False and confirm NOTHING — "couldn't
             check" is never conflated with "proven".
          2. Write a throwaway NON-module scratch file that `import`s the built
             module by name and runs `#print axioms <name>` per target. A non-module
             file makes `#print axioms` legal; importing the olean makes the axiom
             set TRANSITIVE (sees sorry through imports).
          3. Parse each verdict for `sorryAx` and record the full axiom list.
          4. Scan the source for soundness-adjacent patterns (parity with
             lean_verify's scan_source).

        Returns an AxiomSorryResult; use `.is_proven(name)` for the safe verdict.
        """
        if not names:
            return AxiomSorryResult()

        module_name = file_path.replace("/", ".").removesuffix(".lean")
        warnings = self._scan_source_warnings(file_path)

        # 1. Build the module to a fresh olean — no stale cache.
        try:
            build = subprocess.run(
                ["lake", "build", module_name],
                cwd=str(self._root),
                capture_output=True,
                text=True,
                timeout=600,
            )
        except subprocess.TimeoutExpired:
            return AxiomSorryResult(
                build_ok=False, build_error="build timed out (600s)",
                warnings=warnings, error="build timed out (600s)",
            )
        except Exception as e:
            return AxiomSorryResult(
                build_ok=False, build_error=str(e), warnings=warnings, error=str(e),
            )
        if build.returncode != 0:
            out = (build.stdout + "\n" + build.stderr)
            err_lines = [l for l in out.splitlines()
                         if ": error:" in l or "error:" in l.lower()]
            detail = "\n".join(err_lines[:10]) if err_lines else out.strip()[-500:]
            # build failed → confirm nothing (ok=False for every name)
            return AxiomSorryResult(
                build_ok=False, build_error=detail, warnings=warnings,
                ok_by_name={n: False for n in names},
                sorry_by_name={n: True for n in names},
            )

        # 2. Probe from a throwaway NON-module scratch file that imports the olean.
        print_cmds = "\n".join(f"#print axioms {n}" for n in names)
        scratch_content = f"import {module_name}\n\n{print_cmds}\n"
        scratch_rel = f"_mcp_axprobe_{os.getpid()}_{int(time.time() * 1000) % 100000}.lean"
        scratch_abs = self._root / scratch_rel
        try:
            scratch_abs.write_text(scratch_content, encoding="utf-8")
        except Exception as e:
            return AxiomSorryResult(warnings=warnings, error=f"scratch write failed: {e}")

        try:
            probe = subprocess.run(
                ["lake", "env", "lean", scratch_rel],
                cwd=str(self._root),
                capture_output=True,
                text=True,
                timeout=300,
            )
            output = probe.stdout + "\n" + probe.stderr
        except subprocess.TimeoutExpired:
            return AxiomSorryResult(warnings=warnings, error="axiom probe timed out (300s)")
        except Exception as e:
            return AxiomSorryResult(warnings=warnings, error=str(e))
        finally:
            try:
                scratch_abs.unlink()
            except FileNotFoundError:
                pass
            except Exception as exc:
                logger.warning("failed to remove axiom scratch %s: %s", scratch_abs, exc)

        # 3. Parse verdicts. `#print axioms` emits one of:
        #    'X' depends on axioms: [a, b, c]
        #    'X' does not depend on any axioms
        sorry_by_name: dict[str, bool] = {}
        ok_by_name: dict[str, bool] = {}
        axioms_by_name: dict[str, list[str]] = {}
        # Collapse to single line per verdict; messages can wrap.
        flat = output.replace("\n", " ")
        for n in names:
            short = n.rsplit(".", 1)[-1]
            # Match the verdict line for this name (fully-qualified or trailing segment).
            m = re.search(
                rf"'(?:[\w.]*\.)?{re.escape(short)}'\s+"
                rf"(depends on axioms:\s*\[(?P<ax>[^\]]*)\]|does not depend on any axioms)",
                flat,
            )
            if not m:
                ok_by_name[n] = False
                sorry_by_name[n] = True
                axioms_by_name[n] = []
                continue
            ok_by_name[n] = True
            ax_group = m.group("ax")
            axioms = [a.strip() for a in ax_group.split(",")] if ax_group else []
            axioms_by_name[n] = axioms
            sorry_by_name[n] = any("sorryAx" in a for a in axioms)

        return AxiomSorryResult(
            sorry_by_name=sorry_by_name,
            ok_by_name=ok_by_name,
            axioms_by_name=axioms_by_name,
            warnings=warnings,
            build_ok=True,
        )

    def split_theorems(self, file_path: str) -> SplitResult:
        """Get theorem/def blocks with line extents, sorry status, and text.

        Uses itp_interface's TacticParser for proper Lean 4 syntax parsing.
        Handles mutual blocks, noncomputable def, termination_by, etc.
        """
        from itp_interface.lean.tactic_parser import TacticParser, RequestType

        try:
            parser = TacticParser(project_path=str(self._root))
            results, errors = parser.parse_file(file_path, parse_type=RequestType.PARSE_THEOREM)
            parser.close()
        except Exception as e:
            return SplitResult(error=str(e))

        if not results:
            return SplitResult(error=errors[0].message if errors else "No declarations found")

        # Filter to actual declarations (skip open/variable/end/anonymous)
        decl_types = {"theorem", "def", "unknown"}  # unknown = first in mutual block
        blocks = []
        end_lines = []  # track end markers for mutual group detection

        for r in results:
            if r.decl_type == "end" and r.name == "[anonymous]":
                end_lines.append(r.line)
                continue
            if r.decl_type not in decl_types:
                continue
            # Skip open/variable declarations (no text or trivial)
            if not r.text or r.text.strip().startswith("open ") or r.text.strip().startswith("variable "):
                continue

            # Re-derive the real name/kind from the text. The parser lumps a
            # leading modifier (e.g. `set_option warn.sorry false in`, `@[simp]`,
            # `attribute … in`, doc comments) together with the declaration it
            # prefixes into one `unknown` block, and mis-names the block after
            # the modifier (e.g. `warn.sorry`) instead of the theorem. Without
            # this, `set_option warn.sorry false in` would register a phantom
            # sorry-target literally named `warn.sorry`.
            #
            # Some modifier+keyword combos (notably `protected lemma` /
            # `private lemma`) make the parser emit an ANONYMOUS `unknown` block
            # whose text still starts with the real declaration. Recover the name
            # from the text FIRST, and only skip the anonymous block if recovery
            # also fails — otherwise those decls silently vanish from every
            # dependency/target scan (the user asked for full access-modifier
            # coverage, so this must not depend on which modifier is present).
            real_name, real_kind = _real_decl_name(r.text)
            if r.name in ("[anonymous]", "") and not real_name:
                continue
            name = real_name or r.name
            decl_type = real_kind or r.decl_type
            if real_kind is None and not real_name:
                # A block with no real declaration keyword after stripping
                # modifiers (bare `set_option … in`, `open … in`, stray attrs)
                # is not a proof obligation — skip it.
                stripped = _strip_decl_prefixes(r.text)
                if stripped and not re.match(
                    r"(theorem|lemma|def|instance|abbrev|example)\b", stripped):
                    continue

            # Comment-aware: a real `sorry` token, not the word in a doc-comment.
            has_sorry = bool(local_sorry_positions(r.text))
            blocks.append(TheoremBlock(
                name=name,
                start=r.line,
                end=r.end_line,
                has_sorry=has_sorry,
                decl_type=decl_type,
                text=r.text,
            ))

        # Extend block boundaries to include termination_by/decreasing_by clauses
        content = (self._root / file_path).read_text()
        file_lines = content.splitlines()
        for block in blocks:
            # Check lines after block.end for termination_by/decreasing_by
            idx = block.end  # 1-indexed, so file_lines[idx] is the line AFTER block.end
            while idx < len(file_lines):
                line = file_lines[idx].strip()
                if line.startswith("termination_by") or line.startswith("decreasing_by"):
                    block.end = idx + 1  # extend (1-indexed)
                    idx += 1
                elif line == "" or line.startswith("--"):
                    idx += 1  # skip blank/comment lines between them
                else:
                    break
            # Re-derive text and has_sorry with extended boundaries (comment-aware)
            block.text = "\n".join(file_lines[block.start - 1:block.end])
            block.has_sorry = bool(local_sorry_positions(block.text))

        # Detect mutual groups by finding mutual...end ranges in the source
        file_lines = content.splitlines()
        mutual_ranges: list[tuple[int, int]] = []  # (mutual_line, end_line) both 1-indexed
        i = 0
        while i < len(file_lines):
            if file_lines[i].strip() == "mutual":
                mutual_start = i + 1  # 1-indexed
                # Find matching end
                j = i + 1
                while j < len(file_lines) and file_lines[j].strip() != "end":
                    j += 1
                mutual_end = j + 1  # 1-indexed
                mutual_ranges.append((mutual_start, mutual_end))
                i = j + 1
            else:
                i += 1

        mutual_groups: dict[int, list[str]] = {}
        group_id = 0
        for m_start, m_end in mutual_ranges:
            group_members = [b for b in blocks if b.start >= m_start and b.end <= m_end]
            if len(group_members) > 1:
                for b in group_members:
                    b.mutual_group = group_id
                mutual_groups[group_id] = [b.name for b in group_members]
                group_id += 1

        return SplitResult(blocks=blocks, mutual_groups=mutual_groups)

    # ─── Convenience methods ─────────────────────────────────────────────

    def show_file_state(self, file_path: str) -> dict:
        """Complete summary of a Lean file's proof state.

        Returns a dict with:
        - theorems: [{name, status, start_line, end_line, has_sorry, sorry_positions}]
        - sorry_count: total sorries
        - compiles: bool
        - has_error: bool
        - errors: all error diagnostic lines
        - main_theorem: name of last theorem (assumed to be the main one)
        - main_theorem_sorry_free: bool
        """
        import subprocess
        split = self.split_theorems(file_path)

        # ── Single local-sorry source: count, flat positions, per-theorem grouping
        # all come from ONE computation, so they cannot contradict each other. ──
        report = self._local_sorry_report(file_path)
        # A file we cannot read must NEVER read as "sorry-free / compiles" — that is
        # the exact false-negative this consolidation exists to prevent. Surface the
        # error explicitly instead of returning a clean-looking empty state.
        if report["error"]:
            return {
                "theorems": [],
                "sorry_count_local": 0,
                "has_sorry_local": False,
                "has_sorry_transitive": False,
                "compiles": False,
                "has_error": True,
                "errors": [report["error"]],
                "main_theorem": None,
                "main_theorem_sorry_free": False,
            }
        sorry_by_thm = report["by_theorem"]
        local_sorry_count = report["total"]

        # Get full compile output for diagnostics
        errors = []
        try:
            result = subprocess.run(
                ["lake", "env", "lean", file_path],
                cwd=str(self._root),
                capture_output=True, text=True, timeout=120,
            )
            output = result.stdout + "\n" + result.stderr
            # transitive sorry: rely on the specific diagnostic, not a bare "sorry"
            # substring (which would also match file paths / identifiers in output).
            has_sorry = "declaration uses 'sorry'" in output or local_sorry_count > 0
            for line in output.splitlines():
                if ": error:" in line:
                    errors.append(line.strip())
            has_error = len(errors) > 0
            if result.returncode != 0 and not has_error:
                has_error = result.returncode != 0 and not has_sorry
            success = not has_error
        except Exception as e:
            success, has_error, has_sorry = False, True, False
            errors = [str(e)]

        # Detect mutual blocks. Read source unconditionally (a compile error must
        # NOT blank out the structural view — that used to drop mutual groups).
        content = self._read_source(file_path) or ""
        file_lines = content.splitlines() if content else []
        mutual_ranges = []
        i = 0
        while i < len(file_lines):
            if file_lines[i].strip() == "mutual":
                end_i = i + 1
                while end_i < len(file_lines) and file_lines[end_i].strip() != "end":
                    end_i += 1
                mutual_ranges.append((i, end_i))
                i = end_i + 1
            else:
                i += 1

        # Map theorem → mutual group id
        def get_mutual_id(block):
            for idx, (mr_start, mr_end) in enumerate(mutual_ranges):
                if mr_start <= block.start <= mr_end:
                    return idx
            return None

        theorems = []
        for b in (split.blocks if not split.error else []):
            # Per-theorem has_sorry comes from the SINGLE local-sorry report — the
            # same computation that produced the count and flat positions, so a
            # theorem can never read "proved" while the file reports a local sorry.
            thm_positions = sorry_by_thm.get(b.name, [])
            thm_has_sorry = len(thm_positions) > 0
            entry = {
                "name": b.name,
                "status": "sorry" if thm_has_sorry else "proved",
                "start_line": b.start,
                "end_line": b.end,
                "has_sorry": thm_has_sorry,
                "sorry_positions": thm_positions,
            }
            mid = get_mutual_id(b)
            if mid is not None:
                entry["mutual_group"] = mid
            theorems.append(entry)

        main_thm = theorems[-1] if theorems else None

        # Build mutual groups summary
        mutual_groups = {}
        for t in theorems:
            mg = t.get("mutual_group")
            if mg is not None:
                mutual_groups.setdefault(mg, []).append(t["name"])

        # Local sorry facts — straight from the single report, comment-aware.
        local_has_sorry = local_sorry_count > 0

        # main_theorem_sorry_free reflects the main theorem's OWN block only. It is
        # explicitly a LOCAL check: `factLoopM_correct` can be locally sorry-free
        # while still depending on a helper that has a sorry — that transitive fact
        # lives in `has_sorry_transitive` / the axioms oracle, not here. Deriving it
        # from the single per-theorem report keeps it consistent with `theorems`.
        main_sorry_free = (not main_thm["has_sorry"]) if main_thm else True

        result = {
            "theorems": theorems,
            "sorry_count_local": local_sorry_count,
            "has_sorry_local": local_has_sorry,
            "has_sorry_transitive": has_sorry,
            "compiles": success,
            "has_error": has_error,
            "errors": errors,
            "main_theorem": main_thm["name"] if main_thm else None,
            "main_theorem_sorry_free": main_sorry_free,
        }
        if mutual_groups:
            result["mutual_groups"] = mutual_groups
        return result

    def get_sorry_positions(self, file_path: str) -> list[dict]:
        """Get all sorry positions in a file (comment-aware).

        Returns list of {"line": int, "col": int} (0-indexed).

        View over :meth:`_local_sorry_report` (the single local-sorry source): a
        position-preserving, comment-blanked token scan. This replaces the old Lean
        `sorry_positions` RPC, whose deleting comment-stripper collapsed line
        numbers and mislocated any sorry sitting below a block comment.
        """
        return self._local_sorry_report(file_path)["positions"]

    def get_sorries_by_theorem(self, file_path: str, filter_names: list[str] | None = None) -> dict:
        """Get sorry positions grouped by theorem name.

        View over :meth:`_local_sorry_report` (the single local-sorry source),
        which already groups positions into declaration blocks. Because the count,
        the flat positions, and this per-theorem breakdown all come from that one
        computation, they can never contradict each other.

        Args:
            file_path: Relative path from project root.
            filter_names: If provided, only include these theorem names.
                          If None, include all theorems with sorry.

        Returns:
            {
                "theorem_name": [{"line": int, "col": int}, ...],
                ...
            }
        """
        by_theorem = self._local_sorry_report(file_path)["by_theorem"]
        if filter_names:
            allow = set(filter_names)
            return {k: v for k, v in by_theorem.items() if k in allow}
        return by_theorem

    def thm_depends_on(self, file_path: str, theorem_name: str) -> list[str]:
        """Get which other declarations in the same file are referenced by this one.

        Uses word-boundary regex on the text field to avoid substring false positives
        (e.g. 'sim_terminal' matching inside 'sim_terminal_cmd').
        """
        import re
        split = self.split_theorems(file_path)
        if split.error:
            return []

        target = next((b for b in split.blocks if b.name == theorem_name), None)
        if not target or not target.text:
            return []

        # Get the proof body (after := or := by) to avoid matching the signature.
        # Strip comments FIRST so a name mentioned only in a comment is not counted
        # as a dependency edge (parity with Lean's handleThmDependsOn).
        text = strip_comments(target.text)
        body_start = text.find(":= by")
        if body_start == -1:
            body_start = text.find(":=")
        if body_start != -1:
            text = text[body_start + 2:]

        all_names = [b.name for b in split.blocks if b.name != theorem_name]
        # Sort by length descending so longer names are checked first
        # (avoids 'blockSz' matching before 'blockSz_something')
        all_names.sort(key=len, reverse=True)
        uses = []
        for name in all_names:
            # Word boundary: name must not be preceded/followed by alphanumeric or underscore
            if re.search(r'(?<![a-zA-Z0-9_])' + re.escape(name) + r'(?![a-zA-Z0-9_])', text):
                uses.append(name)
        return uses

    def get_reachable_theorems(self, file_path: str, root_name: str) -> set[str]:
        """Get all declarations transitively reachable from root_name."""
        import re
        split = self.split_theorems(file_path)
        if split.error:
            return {root_name}

        all_names = [b.name for b in split.blocks]
        # Sort by length descending for matching priority
        sorted_names = sorted(all_names, key=len, reverse=True)

        # Build dependency map using word-boundary regex on proof bodies
        deps_map: dict[str, list[str]] = {}
        for block in split.blocks:
            if not block.text:
                deps_map[block.name] = []
                continue
            # Extract proof body. Strip comments FIRST (parity with Lean's
            # handleThmDependsOn) so commented-out names don't create false edges.
            text = strip_comments(block.text)
            body_start = text.find(":= by")
            if body_start == -1:
                body_start = text.find(":=")
            if body_start != -1:
                text = text[body_start + 2:]

            deps = []
            for name in sorted_names:
                if name == block.name:
                    continue
                if re.search(r'(?<![a-zA-Z0-9_])' + re.escape(name) + r'(?![a-zA-Z0-9_])', text):
                    deps.append(name)
            deps_map[block.name] = deps

        # BFS from root
        reachable = set()
        queue = [root_name]
        while queue:
            current = queue.pop()
            if current in reachable:
                continue
            reachable.add(current)
            for dep in deps_map.get(current, []):
                if dep not in reachable:
                    queue.append(dep)
        return reachable

    def transitive_sorry_map(
        self, file_path: str, target_names: list[str]
    ) -> "TransitiveSorryMap":
        """Build the AUTHORITATIVE per-target dependency+sorry overview for the guide.

        Joins three sources into ONE picture so the guide never has to piece it
        together itself (and never reasons from stale memory / snapshot notes):

          1. EDGES  — ``get_reachable_theorems`` gives every in-file declaration
             transitively reachable from each target (syntactic, comment-stripped,
             word-boundary; in-file only, so no dependency-graph memory blowup).
          2. VERDICT — ``axioms_by_theorem`` (`#print axioms` via build + non-module
             scratch import) gives the module-SAFE ``has_transitive_sorry`` per
             declaration. This is the ONLY sound "is it really proven" signal; we
             never run `#print axioms` in-place (illegal inside a `module`).
          3. POSITION — ``get_sorries_by_theorem`` gives literal sorry line/cols
             (from the single comment-aware local-sorry source).

        A target is DONE iff it is build-ok and transitively sorry-free. Otherwise
        the map lists exactly which reachable in-file lemmas still carry a sorry
        (transitively), with their positions — the real pending set.
        """
        result = TransitiveSorryMap(file_path=file_path)

        split = self.split_theorems(file_path)
        if split.error:
            result.error = split.error
            return result
        block_by_name = {b.name: b for b in split.blocks}
        all_names = set(block_by_name)

        # 1. EDGES: reachable in-file decls per target (union for the verdict batch).
        reachable_by_target: dict[str, set[str]] = {}
        names_to_check: set[str] = set()
        for t in target_names:
            reach = self.get_reachable_theorems(file_path, t)
            # keep only decls that actually exist in this file (defensive)
            reach = {n for n in reach if n in all_names} | {t}
            reachable_by_target[t] = reach
            names_to_check |= reach

        # 3. POSITIONS: literal sorry coordinates per theorem (whole file once).
        positions = self.get_sorries_by_theorem(file_path)

        # 2. VERDICT: authoritative transitive-sorry check, batched in ONE build +
        #    one scratch probe over every reachable name.
        ax = self.axioms_by_theorem(file_path, sorted(names_to_check))
        result.build_ok = ax.build_ok
        result.build_error = ax.build_error

        def _transitive_sorry(name: str) -> bool:
            # Authoritative: not proven (has_sorry) per the axioms oracle. If the
            # build failed we can't confirm anything → treat as "unknown/unproven".
            if not ax.build_ok:
                return True
            return ax.sorry_by_name.get(name, True)

        for name in sorted(names_to_check):
            blk = block_by_name.get(name)
            # has_local_sorry from the SINGLE source (comment-aware positions),
            # not the parser's naive substring — so it agrees with sorry_positions.
            result.decls[name] = DeclSorryInfo(
                name=name,
                start=blk.start if blk else 0,
                end=blk.end if blk else 0,
                has_local_sorry=len(positions.get(name, [])) > 0,
                has_transitive_sorry=_transitive_sorry(name),
                sorry_positions=positions.get(name, []),
            )

        for t in target_names:
            reach = reachable_by_target.get(t, {t})
            # Open = reachable decls (INCLUDING the target itself) still carrying a
            # transitive sorry. This count is the guide's progress metric.
            open_deps = sorted(
                n for n in reach
                if result.decls.get(n) and result.decls[n].has_transitive_sorry
            )
            done = ax.build_ok and not _transitive_sorry(t)
            result.targets[t] = TargetSorryInfo(
                name=t,
                done=done,
                open_deps=open_deps,
                reachable=sorted(reach),
            )

        return result

    def has_sorry(self, file_path: str) -> bool:
        """Check if file has a LOCAL sorry (in its own text, incl. decreasing_by sorry).

        View over :meth:`_local_sorry_report` (the single local-sorry source): a
        comment-aware token scan. Does NOT check transitive sorry from imports —
        use :meth:`has_sorry_transitive` for that.
        """
        return self._local_sorry_report(file_path)["total"] > 0

    def has_sorry_transitive(self, file_path: str) -> bool:
        """Check if file or ANY of its imports has sorry (transitive).

        Uses lake build output — "declaration uses sorry" warnings from deps.
        More expensive than has_sorry() but gives the complete picture.
        """
        cr = self.check_compiles(file_path)
        return cr.has_sorry

    def is_proved(self, file_path: str) -> bool:
        """Quick check: is the file sorry-free?"""
        return not self.has_sorry(file_path)

    def sorry_theorem_names(self, file_path: str) -> list[str]:
        """Get names of theorems that have sorry."""
        result = self.list_theorems(file_path)
        return [t.name for t in result.theorems if t.status == "sorry"]

    def check_dag(self, file_path: str, workspace_module: str) -> list[str]:
        """Check DAG violations: imports from outside workspace that are in Sandbox."""
        result = self.check_imports(file_path)
        if result.error:
            return []
        bad = []
        for imp in result.imports:
            if imp.startswith("StrataAgent.Sandbox") and not imp.startswith(workspace_module):
                bad.append(imp)
        return bad

    # ─── Refactoring: extract sorry theorems into separate files ─────────

    def extract_sorry_theorems(self, file_path: str, output_dir: str | None = None, exclude: set[str] | None = None, extract_all: bool = False) -> ExtractResult:
        """Extract sorry theorems from a file into individual files for child POs.

        The original file is LEFT UNCHANGED — it already compiles (with sorry
        warnings from the inline helper definitions). Child POs prove each helper
        independently, and assembly copies the proved versions back.

        What this does:
        1. Identifies sorry theorem blocks via split_theorems_
        2. Copies each sorry theorem (with header) into its own file
        3. Returns the list of created files for child PO spawning

        The original keeps working as-is. No import rewriting needed.

        Naming: lemma_helper_<ascii_escaped_theorem_name>.lean
        """
        root = self._root
        source = root / file_path
        if not source.exists():
            return ExtractResult(error=f"File not found: {file_path}")

        split = self.split_theorems(file_path)
        if split.error:
            return ExtractResult(error=split.error)

        if extract_all:
            # Extract every theorem except excluded ones
            target_blocks = [b for b in split.blocks if (not exclude or b.name not in exclude)]
        else:
            # Extract only sorry theorems
            target_blocks = [b for b in split.blocks if b.has_sorry and (not exclude or b.name not in exclude)]

        if not target_blocks:
            return ExtractResult(skipped=True, reason="no theorems to extract")

        # Filter to reachable from main theorem (avoid extracting dead helpers)
        if exclude:
            main_name = next(iter(exclude))
            reachable = self.get_reachable_theorems(file_path, main_name)
            target_blocks = [b for b in target_blocks if b.name in reachable]
            if not target_blocks:
                return ExtractResult(skipped=True, reason="no reachable theorems to extract")

        content = source.read_text()
        lines = content.splitlines()

        # Header = everything before first declaration (imports, open, variable)
        first_decl_line = min(b.start for b in split.blocks) - 1 if split.blocks else 0
        header_lines = [l for l in lines[:first_decl_line]
                        if not l.strip().startswith("/-") and not l.strip().startswith("--")
                        and l.strip() not in ("mutual", "end")]
        header = "\n".join(header_lines)

        # Output directory
        if output_dir:
            out_path = root / output_dir
        else:
            out_path = source.parent
        out_path.mkdir(parents=True, exist_ok=True)

        # ── Step 1: Group by mutual blocks ──
        groups: list[list[TheoremBlock]] = []
        seen = set()
        for block in target_blocks:
            if block.name in seen:
                continue
            if block.mutual_group is not None:
                group = [b for b in target_blocks if b.mutual_group == block.mutual_group]
                for b in group:
                    seen.add(b.name)
                groups.append(group)
            else:
                seen.add(block.name)
                groups.append([block])

        # ── Step 2: Build dependency graph between groups ──
        extracted_name_set = {b.name for b in target_blocks}
        # Per-block deps (text-based)
        block_deps: dict[str, list[str]] = {}
        for block in target_blocks:
            block_deps[block.name] = [n for n in extracted_name_set
                                       if n != block.name and n in (block.text or "")]

        # Map name → group index
        name_to_gi: dict[str, int] = {}
        for gi, group in enumerate(groups):
            for b in group:
                name_to_gi[b.name] = gi

        # Group-level deps
        group_deps: dict[int, set[int]] = {i: set() for i in range(len(groups))}
        for gi, group in enumerate(groups):
            for b in group:
                for dep_name in block_deps.get(b.name, []):
                    dep_gi = name_to_gi.get(dep_name)
                    if dep_gi is not None and dep_gi != gi:
                        group_deps[gi].add(dep_gi)

        # ── Step 3: Find SCCs and merge cyclic groups ──
        merged = True
        while merged:
            merged = False
            # Rebuild group index mapping
            name_to_gi = {}
            for gi, group in enumerate(groups):
                for b in group:
                    name_to_gi[b.name] = gi
            group_deps = {i: set() for i in range(len(groups))}
            for gi, group in enumerate(groups):
                for b in group:
                    for dep_name in block_deps.get(b.name, []):
                        dep_gi = name_to_gi.get(dep_name)
                        if dep_gi is not None and dep_gi != gi:
                            group_deps[gi].add(dep_gi)
            # Merge any cycle
            for gi in range(len(groups)):
                for gj in group_deps.get(gi, set()):
                    if gi in group_deps.get(gj, set()):
                        groups[gi] = groups[gi] + groups[gj]
                        groups.pop(gj)
                        merged = True
                        break
                if merged:
                    break

        # ── Step 4: Topological sort ──
        # Rebuild after merging
        name_to_gi = {}
        for gi, group in enumerate(groups):
            for b in group:
                name_to_gi[b.name] = gi
        group_deps = {i: set() for i in range(len(groups))}
        for gi, group in enumerate(groups):
            for b in group:
                for dep_name in block_deps.get(b.name, []):
                    dep_gi = name_to_gi.get(dep_name)
                    if dep_gi is not None and dep_gi != gi:
                        group_deps[gi].add(dep_gi)

        # Kahn's algorithm
        in_degree = {i: 0 for i in range(len(groups))}
        for gi, deps in group_deps.items():
            for dep_gi in deps:
                in_degree[gi] = in_degree.get(gi, 0)  # ensure exists
        for gi, deps in group_deps.items():
            for dep_gi in deps:
                in_degree[gi] += 1  # gi depends on dep_gi, so gi has in-degree from dep_gi
        # Wait — in_degree should count how many things point TO a node
        # If gi depends on dep_gi, then dep_gi must come first. So dep_gi has
        # an edge pointing to gi. in_degree[gi] = number of deps gi has.
        in_degree = {i: len(group_deps.get(i, set())) for i in range(len(groups))}
        # Reverse graph: who depends on me?
        rev_deps: dict[int, set[int]] = {i: set() for i in range(len(groups))}
        for gi, deps in group_deps.items():
            for dep_gi in deps:
                rev_deps[dep_gi].add(gi)

        topo_order = []
        queue = [i for i in range(len(groups)) if in_degree[i] == 0]
        while queue:
            node = queue.pop(0)
            topo_order.append(node)
            for dependent in rev_deps.get(node, set()):
                in_degree[dependent] -= 1
                if in_degree[dependent] == 0:
                    queue.append(dependent)
        # Any remaining (shouldn't happen after SCC merge) go at end
        for i in range(len(groups)):
            if i not in topo_order:
                topo_order.append(i)

        # ── Step 5: Write files in topological order ──
        import subprocess
        out_rel = str(out_path.relative_to(root))
        name_to_module: dict[str, str] = {}
        created_files: list[str] = []
        extracted_names: list[str] = []

        for gi in topo_order:
            group = groups[gi]

            # Determine file name/module
            safe_name = _ascii_escape(group[0].name)
            module = f"{out_rel}/lemma_helper_{safe_name}".replace("/", ".")
            for b in group:
                name_to_module[b.name] = module

            # Build block text
            if len(group) > 1:
                # Multiple declarations: grab raw lines (mutual...end)
                first_line = min(b.start for b in group) - 1
                last_line = max(b.end for b in group)
                end_idx = last_line
                while end_idx < len(lines) and lines[end_idx].strip() != "end":
                    end_idx += 1
                block_lines = lines[first_line:end_idx + 1]
                block_lines = [l.replace("private theorem ", "theorem ")
                                .replace("private def ", "def ")
                                .replace("private noncomputable def ", "noncomputable def ")
                               for l in block_lines]
                block_text = "\n".join(block_lines)
            else:
                block = group[0]
                block_text = block.text
                block_text = block_text.replace("private theorem ", "theorem ", 1)
                block_text = block_text.replace("private def ", "def ", 1)
                block_text = block_text.replace("private noncomputable def ", "noncomputable def ", 1)

            # Compute imports: only from earlier groups in topo order
            # Then prune transitive redundancies
            group_names = {b.name for b in group}
            dep_group_idxs = set()
            for b in group:
                for dep_name in block_deps.get(b.name, []):
                    if dep_name not in group_names and dep_name in name_to_gi:
                        dep_group_idxs.add(name_to_gi[dep_name])

            # Prune: remove dep groups that are transitively reachable from other dep groups
            # (i.e. if A depends on B depends on C, and we depend on both A and C, drop C)
            minimal_deps = set(dep_group_idxs)
            for dgi in list(dep_group_idxs):
                # Check if dgi is reachable from any other dep via group_deps
                others = dep_group_idxs - {dgi}
                reachable_from_others = set()
                q = list(others)
                visited = set()
                while q:
                    curr = q.pop()
                    if curr in visited:
                        continue
                    visited.add(curr)
                    reachable_from_others.add(curr)
                    q.extend(group_deps.get(curr, set()))
                if dgi in reachable_from_others:
                    minimal_deps.discard(dgi)

            dep_imports = set()
            for dgi in minimal_deps:
                # Get the module name for this dep group
                dep_group = groups[dgi]
                dep_safe_name = _ascii_escape(dep_group[0].name)
                dep_module = f"{out_rel}/lemma_helper_{dep_safe_name}".replace("/", ".")
                dep_imports.add(f"import {dep_module}")

            # Write file
            new_filename = f"lemma_helper_{safe_name}.lean"
            new_path = out_path / new_filename
            h_lines = header.rstrip().splitlines()
            if dep_imports:
                insert_pos = 0
                for idx, hl in enumerate(h_lines):
                    if hl.strip().startswith("import "):
                        insert_pos = idx + 1
                for idx, imp in enumerate(sorted(dep_imports)):
                    h_lines.insert(insert_pos + idx, imp)
            new_content = "\n".join(h_lines) + "\n\n" + block_text + "\n"
            new_path.write_text(new_content)

            # Build immediately (deps already built due to topo order)
            file_module = f"{out_rel}/lemma_helper_{safe_name}".replace("/", ".")
            build_result = subprocess.run(["lake", "build", file_module],
                          cwd=str(root), capture_output=True, text=True, timeout=120)

            # Handle "environment already contains X from Y" conflicts
            # by removing the redundant import (the symbol is available transitively)
            if build_result.returncode != 0 and "environment already contains" in (build_result.stdout + build_result.stderr):
                import re
                output = build_result.stdout + build_result.stderr
                # May have multiple conflicts — remove all bad imports
                bad_imports = set()
                for match in re.finditer(r"import (\S+) failed", output):
                    bad_imports.add(match.group(1))
                if bad_imports:
                    file_content = new_path.read_text()
                    fixed_lines = [l for l in file_content.splitlines()
                                   if not any(l.strip() == f"import {bi}" for bi in bad_imports)]
                    new_path.write_text("\n".join(fixed_lines) + "\n")
                    # Also remove from the stmtSz import if that's the source
                    for conflict_src in re.finditer(r"from (\S+)", output):
                        src_module = conflict_src.group(1)
                        if src_module in [l.strip().removeprefix("import ") for l in fixed_lines if l.strip().startswith("import ")]:
                            fixed_lines = [l for l in fixed_lines
                                           if l.strip() != f"import {src_module}"]
                            new_path.write_text("\n".join(fixed_lines) + "\n")
                            break
                    subprocess.run(["lake", "build", file_module],
                                  cwd=str(root), capture_output=True, timeout=120)

            rel_path = str(new_path.relative_to(root))
            created_files.append(rel_path)
            extracted_names.extend(b.name for b in group)

        # Verify: each extracted file should compile (with sorry)
        failed_files: list[str] = []
        for f in created_files:
            cr = self.check_compiles(f)
            if not cr.success:
                failed_files.append(f)

        if failed_files:
            # Move failed extractions to extraction_failed/ for debugging
            failed_dir = out_path / "extraction_failed"
            failed_dir.mkdir(exist_ok=True)
            for f in failed_files:
                src_file = root / f
                if src_file.exists():
                    shutil.move(str(src_file), str(failed_dir / src_file.name))
            failed_set = set(failed_files)
            surviving = [(f, n) for f, n in zip(created_files, extracted_names) if f not in failed_set]
            created_files = [f for f, _ in surviving]
            extracted_names = [n for _, n in surviving]

        if not created_files:
            return ExtractResult(error="All extracted files failed to compile")

        return ExtractResult(
            created_files=created_files,
            extracted_names=extracted_names,
            original_updated=file_path,
        )

    def refactor_file(self, file_path: str, output_dir: str | None = None) -> ExtractResult:
        """Refactor a file so every theorem is in its own file.

        - Proved theorems stay in the original (dependencies for others).
        - Sorry theorems each get their own file.
        - If there's only one theorem total (sorry or not), no action taken.

        This is the main entry point for the REFACTOR stage of the PO pipeline.

        Args:
            file_path: Relative path to the source file.
            output_dir: Directory for extracted files. Defaults to same dir as source.

        Returns:
            ExtractResult. If skipped=True, no changes were made.
        """
        root = self._root
        source = root / file_path
        if not source.exists():
            return ExtractResult(error=f"File not found: {file_path}")

        split = self.split_theorems(file_path)
        if split.error:
            return ExtractResult(error=split.error)

        sorry_blocks = [b for b in split.blocks if b.has_sorry]

        # Nothing to refactor: 0 or 1 total theorems, or no sorry theorems
        if len(split.blocks) <= 1:
            return ExtractResult(skipped=True, reason="single theorem file — nothing to refactor")
        if not sorry_blocks:
            return ExtractResult(skipped=True, reason="all theorems proved — nothing to extract")

        return self.extract_sorry_theorems(file_path, output_dir=output_dir)

    # ─── Write decomposed lemma (verified) ────────────────────────────────

    def write_decomposed_lemma(self, file_content: str, theorem_name: str,
                                output_dir: str) -> WriteResult:
        """Write a single decomposed lemma file with verification.

        Enforces:
        1. Exactly one theorem in the file (the named one)
        2. theorem_name matches the theorem found in content
        3. The file compiles (sorry OK, real errors not)

        Naming: lemma_helper_<ascii_escaped_theorem_name>.lean

        Args:
            file_content: Full Lean file content (imports + theorem + sorry body)
            theorem_name: Expected theorem name
            output_dir: Relative path for output (e.g. "StrataAgent/Sandbox/decomposed")

        Returns:
            WriteResult with file path and any verification errors.
        """
        root = self._root
        out_path = root / output_dir
        out_path.mkdir(parents=True, exist_ok=True)

        safe_name = _ascii_escape(theorem_name)
        filename = f"lemma_helper_{safe_name}.lean"
        file_path = out_path / filename
        rel_path = f"{output_dir}/{filename}"

        # Write the file (needed on disk for Lean tools to check it)
        file_path.write_text(file_content.rstrip() + "\n")

        # Verify 0: reject axiom keyword (definitive, comment-aware check)
        axiom_check = self.check_axioms(rel_path)
        if axiom_check.has_axiom:
            file_path.unlink(missing_ok=True)
            return WriteResult(
                error=f"File contains `axiom` declarations which are UNSOUND: {axiom_check.axiom_names}. "
                      f"Use `theorem ... := by sorry` instead.")

        # Verify 1: exactly one theorem
        split = self.split_theorems(rel_path)
        if split.error:
            file_path.unlink(missing_ok=True)
            return WriteResult(error=f"parse error: {split.error}")

        if len(split.blocks) != 1:
            file_path.unlink(missing_ok=True)
            return WriteResult(
                error=f"Expected exactly 1 theorem, found {len(split.blocks)}: "
                      f"{[b.name for b in split.blocks]}")

        # Verify 2: theorem name matches
        actual_name = split.blocks[0].name
        if actual_name != theorem_name:
            file_path.unlink(missing_ok=True)
            return WriteResult(
                error=f"Theorem name mismatch: expected '{theorem_name}', found '{actual_name}'")

        # Verify 3: compiles
        cr = self.check_compiles(rel_path)
        if cr.has_error:
            file_path.unlink(missing_ok=True)
            return WriteResult(error=f"Does not compile")

        return WriteResult(file_path=rel_path, theorem_name=actual_name, has_sorry=cr.has_sorry)

    # ─── write_helper_lemma (v3 transactional tool) ────────────────────

    def write_helper_lemma(self, theorem_name: str, theorem_statement: str,
                           additional_imports: list[str],
                           sorry_line: int, sorry_col: int,
                           replacement_tactic: str,
                           target_file: str, workspace: str) -> WriteResult:
        """Transactional: create helper file + replace sorry in target.

        Order of operations (line numbers stay valid):
        1. Build helper file (parent header + additional_imports + theorem_statement)
        2. Write to decomposed/lemma_helper_<name>.lean, verify compiles
        3. Backup target
        4. Replace sorry at (line, col) with replacement_tactic (original line numbers)
        5. Add import for helper at top (AFTER replacement, so line nums were valid)
        6. Verify target compiles
        7. If ANY step fails → revert everything

        Args:
            theorem_name: Name of the helper theorem
            theorem_statement: Full theorem (e.g. "theorem foo ... := by sorry")
            additional_imports: Extra imports helper needs beyond parent header
            sorry_line: 0-indexed line of the sorry in the ORIGINAL target file
            sorry_col: Column of the sorry
            replacement_tactic: What replaces sorry (e.g. "exact foo x h")
            target_file: Relative path to file containing the sorry
            workspace: Workspace relative path

        Returns:
            WriteResult with helper file_path on success, error on failure.
        """
        root = self._root
        target_path = root / target_file

        if not target_path.exists():
            return WriteResult(error=f"Target file not found: {target_file}")

        target_content = target_path.read_text()
        target_lines = target_content.splitlines()

        # Extract header from target (imports + open + variable)
        header_lines = []
        for line in target_lines:
            stripped = line.strip()
            if (stripped.startswith("import ") or stripped.startswith("open ") or
                    stripped.startswith("variable ") or stripped.startswith("set_option") or
                    stripped.startswith("/-") or stripped.startswith("--") or not stripped):
                header_lines.append(line)
            else:
                break
        header = "\n".join(header_lines)

        # ── Step 1: Build helper file ──
        helper_imports = header.rstrip()
        if additional_imports:
            helper_imports += "\n" + "\n".join(additional_imports)
        helper_content = helper_imports + "\n\n" + theorem_statement.rstrip() + "\n"

        # ── Step 2: Write and verify helper ──
        out_dir = root / workspace / "decomposed"
        out_dir.mkdir(parents=True, exist_ok=True)

        safe_name = _ascii_escape(theorem_name)
        helper_filename = f"lemma_helper_{safe_name}.lean"
        helper_path = out_dir / helper_filename
        helper_rel = f"{workspace}/decomposed/{helper_filename}"

        helper_path.write_text(helper_content)

        cr = self.check_compiles(helper_rel)
        if not cr.success:
            helper_path.unlink(missing_ok=True)
            return WriteResult(error=f"Helper does not compile")

        ax = self.check_axioms(helper_rel)
        if ax.has_axiom:
            helper_path.unlink(missing_ok=True)
            return WriteResult(error=f"Helper uses axiom: {ax.axiom_names}")

        split = self.split_theorems(helper_rel)
        if split.error or len(split.blocks) != 1:
            helper_path.unlink(missing_ok=True)
            return WriteResult(error=f"Helper must have exactly 1 theorem")

        if split.blocks[0].name != theorem_name:
            helper_path.unlink(missing_ok=True)
            return WriteResult(error=f"Name mismatch: expected '{theorem_name}', got '{split.blocks[0].name}'")

        # Build helper .olean (required before other files can import it)
        helper_module = helper_rel.replace("/", ".").removesuffix(".lean")
        build = subprocess.run(
            ["lake", "build", helper_module],
            cwd=str(root), capture_output=True, text=True, timeout=120,
        )
        if build.returncode != 0:
            helper_path.unlink(missing_ok=True)
            return WriteResult(error=f"Helper failed to build: {(build.stdout + build.stderr)[:200]}")

        # ── Step 3: Backup target ──
        backup_path = root / f"{target_file}.helper_bak"
        shutil.copy2(target_path, backup_path)

        # ── Step 4: Replace sorry at (line, col) — using ORIGINAL line numbers ──
        if sorry_line >= len(target_lines):
            helper_path.unlink(missing_ok=True)
            backup_path.unlink(missing_ok=True)
            return WriteResult(error=f"sorry_line {sorry_line} out of range ({len(target_lines)} lines)")

        line_content = target_lines[sorry_line]
        sorry_idx = line_content.find("sorry", sorry_col)
        if sorry_idx == -1:
            sorry_idx = line_content.find("sorry")
        if sorry_idx == -1:
            helper_path.unlink(missing_ok=True)
            backup_path.unlink(missing_ok=True)
            return WriteResult(error=f"No 'sorry' at line {sorry_line} (content: {line_content.strip()!r})")

        target_lines[sorry_line] = line_content[:sorry_idx] + replacement_tactic + line_content[sorry_idx + 5:]

        # ── Step 5: Add import AFTER replacement (so line nums were valid above) ──
        import_module = helper_rel.replace("/", ".").removesuffix(".lean")
        import_line = f"import {import_module}"

        last_import_idx = -1
        for i, line in enumerate(target_lines):
            if line.strip().startswith("import "):
                last_import_idx = i
        if last_import_idx >= 0:
            target_lines.insert(last_import_idx + 1, import_line)
        else:
            target_lines.insert(0, import_line)

        # Write modified target
        target_path.write_text("\n".join(target_lines) + "\n")

        # ── Step 6: Verify target compiles ──
        cr = self.check_compiles(target_file)
        if not cr.success:
            shutil.copy2(backup_path, target_path)
            backup_path.unlink(missing_ok=True)
            helper_path.unlink(missing_ok=True)
            return WriteResult(
                error=f"Target doesn't compile after replacement. "
                      f"'{replacement_tactic}' may not type-check at this goal.")

        # ── Success ──
        backup_path.unlink(missing_ok=True)
        return WriteResult(file_path=helper_rel, theorem_name=theorem_name, has_sorry=True)

    # ─── Lifecycle ───────────────────────────────────────────────────────

    def close(self):
        """Shut down the process."""
        self._kill()

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    def __del__(self):
        self.close()


# ─── Module-level singleton (lazy) ───────────────────────────────────────────

_instance: SwarmLeanTools | None = None


def get_lean_tools() -> SwarmLeanTools:
    """Get or create the singleton SwarmLeanTools instance."""
    global _instance
    if _instance is None:
        _instance = SwarmLeanTools()
    return _instance
