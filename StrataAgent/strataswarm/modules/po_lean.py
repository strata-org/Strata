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


def _ascii_escape(name: str) -> str:
    """Escape a theorem name to a safe ASCII filename component.
    Keeps alphanumeric + underscore, replaces everything else with _."""
    return "".join(c if c.isalnum() or c == "_" else "_" for c in name)[:60]


@dataclass
class AxiomCheckResult:
    has_axiom: bool = False
    axiom_names: list[str] = field(default_factory=list)
    error: str | None = None


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

    def __init__(self, tools: "SwarmLeanTools", file_path: str, main_theorem: str, workspace: str):
        self._tools = tools
        self._file_path = file_path
        self._main_theorem = main_theorem
        self._workspace = workspace
        self._moves: list[MoveIntent] = []
        self._split: SplitResult | None = None
        self._backup: str | None = None  # original file content
        self._committed = False

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
        """Execute all moves: write files, rewrite Stub.lean, build, verify."""
        import subprocess

        root = self._tools._root
        source = root / self._file_path
        content = source.read_text()
        lines = content.splitlines()

        if not self._split:
            self._split = self._tools.split_theorems(self._file_path)
        if self._split.error:
            return ExtractResult(error=self._split.error)

        # Header (imports, open, variable — before first decl)
        first_decl_line = min(b.start for b in self._split.blocks) - 1 if self._split.blocks else 0
        header_lines = [l for l in lines[:first_decl_line]
                        if not l.strip().startswith("/-") and not l.strip().startswith("--")
                        and l.strip() not in ("mutual", "end")]
        header = "\n".join(header_lines)

        # Output directory
        out_path = root / self._workspace / "decomposed"
        out_path.mkdir(parents=True, exist_ok=True)
        out_rel = str(out_path.relative_to(root))

        # Build name → module mapping
        name_to_module: dict[str, str] = {}
        for move in self._moves:
            safe_name = _ascii_escape(move.decl_name)
            module = f"{out_rel}/lemma_helper_{safe_name}".replace("/", ".")
            # Map all members if mutual
            block = next((b for b in self._split.blocks if b.name == move.decl_name), None)
            if block and block.mutual_group is not None:
                for member_name in self._split.mutual_groups.get(block.mutual_group, []):
                    name_to_module[member_name] = module
            else:
                name_to_module[move.decl_name] = module

        # Write each moved declaration to its own file
        created_files: list[str] = []
        extracted_names: list[str] = []

        for move in self._moves:
            block = next((b for b in self._split.blocks if b.name == move.decl_name), None)
            if not block:
                continue

            # Get block text
            if block.mutual_group is not None:
                # Mutual: grab raw lines from file (mutual...end inclusive)
                group_blocks = [b for b in self._split.blocks if b.mutual_group == block.mutual_group]
                first_line = min(b.start for b in group_blocks) - 1
                last_line = max(b.end for b in group_blocks)
                end_idx = last_line
                while end_idx < len(lines) and lines[end_idx].strip() != "end":
                    end_idx += 1
                block_lines = lines[first_line:end_idx + 1]
                block_lines = [l.replace("private theorem ", "theorem ")
                                .replace("private def ", "def ")
                                .replace("private noncomputable def ", "noncomputable def ")
                               for l in block_lines]
                block_text = "\n".join(block_lines)
                group_names = [b.name for b in group_blocks]
            else:
                block_text = block.text
                block_text = block_text.replace("private theorem ", "theorem ", 1)
                block_text = block_text.replace("private def ", "def ", 1)
                block_text = block_text.replace("private noncomputable def ", "noncomputable def ", 1)
                group_names = [block.name]

            # Build imports from additional_imports
            dep_imports = []
            for dep_name in move.additional_imports:
                if dep_name in name_to_module:
                    imp = f"import {name_to_module[dep_name]}"
                    if imp not in dep_imports:
                        dep_imports.append(imp)

            # Write file
            safe_name = _ascii_escape(move.decl_name)
            new_filename = f"lemma_helper_{safe_name}.lean"
            new_path = out_path / new_filename

            h_lines = header.rstrip().splitlines()
            if dep_imports:
                insert_pos = 0
                for idx, hl in enumerate(h_lines):
                    if hl.strip().startswith("import "):
                        insert_pos = idx + 1
                for idx, imp in enumerate(dep_imports):
                    h_lines.insert(insert_pos + idx, imp)
            new_content = "\n".join(h_lines) + "\n\n" + block_text + "\n"
            new_path.write_text(new_content)

            rel_path = str(new_path.relative_to(root))
            created_files.append(rel_path)
            extracted_names.extend(group_names)

        # Rewrite Stub.lean: header + all imports + main theorem only
        main_block = next((b for b in self._split.blocks if b.name == self._main_theorem), None)
        if not main_block:
            return ExtractResult(error=f"Main theorem '{self._main_theorem}' not found")

        import_lines = [f"import {name_to_module[m.decl_name]}" for m in self._moves
                        if m.decl_name in name_to_module]
        h_lines = header.rstrip().splitlines()
        insert_pos = 0
        for idx, hl in enumerate(h_lines):
            if hl.strip().startswith("import "):
                insert_pos = idx + 1
        for idx, imp in enumerate(import_lines):
            h_lines.insert(insert_pos + idx, imp)

        main_text = main_block.text
        new_stub = "\n".join(h_lines) + "\n\n" + main_text + "\n"
        source.write_text(new_stub)

        # Build all decomposed files then Stub.lean
        for f in created_files:
            module = f.replace("/", ".").removesuffix(".lean")
            subprocess.run(["lake", "build", module],
                          cwd=str(root), capture_output=True, timeout=120)

        # Verify Stub.lean compiles sorry-free
        cr = self._tools.check_compiles(self._file_path)
        has_sorry = self._tools.has_sorry(self._file_path)

        self._committed = True
        self._created_files = created_files
        self._extracted_names = extracted_names

        if not cr.success or has_sorry:
            error_msg = "Stub.lean doesn't compile after extraction" if not cr.success else "Stub.lean still has sorry"
            return ExtractResult(error=error_msg, created_files=created_files, extracted_names=extracted_names)

        return ExtractResult(created_files=created_files, extracted_names=extracted_names)

    def revert(self) -> str:
        """Undo everything: restore original Stub.lean, remove decomposed files."""
        root = self._tools._root
        source = root / self._file_path

        if self._backup is None:
            return "Error: no backup available (get_declarations not called?)"

        # Restore original file
        source.write_text(self._backup)

        # Remove decomposed files we created
        out_path = root / self._workspace / "decomposed"
        if out_path.exists():
            shutil.rmtree(out_path)

        # Reset state for retry
        self._moves.clear()
        self._committed = False
        self._split = None

        return "OK: reverted to original"

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

    def count_sorries(self, file_path: str) -> SorryInfo:
        """Count sorries in a file. Returns per-declaration breakdown."""
        result = self._send("count__sorries_", file_path)
        if "error" in result:
            return SorryInfo(error=result["error"])
        return SorryInfo(
            total=result.get("total", 0),
            sorry_decls=result.get("sorry_decls", []),
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
        """Check if a file compiles. Uses lake build for reliable dependency handling.

        Falls back to lake env lean if lake build can't determine the module name.
        """
        import subprocess
        try:
            # Prefer lake build (handles olean rebuilds)
            module_name = file_path.replace("/", ".").removesuffix(".lean")
            result = subprocess.run(
                ["lake", "build", module_name],
                cwd=str(self._root),
                capture_output=True,
                text=True,
                timeout=120,
            )
            # If lake build fails, fall back to lake env lean for error diagnostics
            if result.returncode != 0:
                result = subprocess.run(
                    ["lake", "env", "lean", file_path],
                    cwd=str(self._root),
                    capture_output=True,
                    text=True,
                    timeout=120,
                )
            # Lean outputs diagnostics on stdout; check both stdout and stderr
            output = result.stdout + "\n" + result.stderr
            has_sorry = "sorry" in output or "declaration uses 'sorry'" in output
            has_error = any(
                ": error:" in line and "sorry" not in line
                for line in output.splitlines()
            )
            # Also treat non-zero exit code as error (unless only sorry warnings)
            if result.returncode != 0 and not has_error:
                # Check if the only issues are sorry warnings
                has_error = result.returncode != 0 and not has_sorry
            success = not has_error
            return CompileResult(success=success, has_sorry=has_sorry, has_error=has_error)
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
            if r.name in ("[anonymous]", ""):
                continue
            # Skip open/variable declarations (no text or trivial)
            if not r.text or r.text.strip().startswith("open ") or r.text.strip().startswith("variable "):
                continue

            has_sorry = "sorry" in r.text
            blocks.append(TheoremBlock(
                name=r.name,
                start=r.line,
                end=r.end_line,
                has_sorry=has_sorry,
                decl_type=r.decl_type,
                text=r.text,
            ))

        # Detect mutual groups by finding mutual...end ranges in the source
        content = (self._root / file_path).read_text()
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
        sorry_info = self.count_sorries(file_path)

        # Get full compile output for diagnostics
        errors = []
        try:
            result = subprocess.run(
                ["lake", "env", "lean", file_path],
                cwd=str(self._root),
                capture_output=True, text=True, timeout=120,
            )
            output = result.stdout + "\n" + result.stderr
            has_sorry = "sorry" in output or "declaration uses 'sorry'" in output
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

        # Get sorry positions grouped by theorem
        sorry_by_thm = self.get_sorries_by_theorem(file_path)

        # Detect mutual blocks
        content = (self._root / file_path).read_text() if not errors else ""
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
            entry = {
                "name": b.name,
                "status": "sorry" if b.has_sorry else "proved",
                "start_line": b.start,
                "end_line": b.end,
                "has_sorry": b.has_sorry,
                "sorry_positions": sorry_by_thm.get(b.name, []),
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

        result = {
            "theorems": theorems,
            "sorry_count": sorry_info.total,
            "compiles": success,
            "has_error": has_error,
            "errors": errors,
            "main_theorem": main_thm["name"] if main_thm else None,
            "main_theorem_sorry_free": (not main_thm["has_sorry"]) if main_thm else False,
        }
        if mutual_groups:
            result["mutual_groups"] = mutual_groups
        return result

    def get_sorry_positions(self, file_path: str) -> list[dict]:
        """Get all sorry positions in a file (comment-aware).

        Returns list of {"line": int, "col": int} (0-indexed).
        Uses the Lean RPC which strips comments before scanning.
        """
        result = self._send("sorry_positions", file_path)
        if "error" in result:
            return []
        return result.get("positions", [])

    def get_sorries_by_theorem(self, file_path: str, filter_names: list[str] | None = None) -> dict:
        """Get sorry positions grouped by theorem name.

        Combines split_theorems_ (for block boundaries) with sorry_positions
        (for exact coordinates) to produce a per-theorem breakdown.

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
        split = self.split_theorems(file_path)
        if split.error:
            return {}

        positions = self.get_sorry_positions(file_path)
        if not positions:
            return {}

        # Group sorry positions by which theorem block they fall in
        # sorry_positions from SwarmAgentTools are 0-indexed
        # block.start/end from itp_interface TacticParser are 1-indexed
        result = {}
        for block in split.blocks:
            if not block.has_sorry:
                continue
            if filter_names and block.name not in filter_names:
                continue

            block_sorries = []
            for pos in positions:
                pos_1indexed = pos["line"] + 1
                if block.start <= pos_1indexed <= block.end:
                    block_sorries.append(pos)

            if block_sorries:
                result[block.name] = block_sorries

        return result

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

        # Get the proof body (after := or := by) to avoid matching the signature
        text = target.text
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
            # Extract proof body
            text = block.text
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

    def has_sorry(self, file_path: str) -> bool:
        """Quick check: does the file have any sorry?"""
        info = self.count_sorries(file_path)
        return info.total > 0

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
