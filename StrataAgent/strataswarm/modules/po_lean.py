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
        """Check if a file compiles. Runs lake env lean directly from Python.

        NOTE: lake env lean outputs diagnostics on STDOUT (not stderr).
        We check both to be safe.
        """
        import subprocess
        try:
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
        content = source.read_text() if not errors else ""
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
        """Get which other theorems in the same file are referenced by this theorem's proof."""
        result = self._send("thm_depends_on_", f"{file_path}:{theorem_name}")
        if "error" in result:
            return []
        return result.get("uses", [])

    def get_reachable_theorems(self, file_path: str, root_name: str) -> set[str]:
        """Get all theorems transitively reachable from root_name's proof body."""
        reachable = set()
        queue = [root_name]
        while queue:
            current = queue.pop()
            if current in reachable:
                continue
            reachable.add(current)
            deps = self.thm_depends_on(file_path, current)
            queue.extend(d for d in deps if d not in reachable)
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
        # Use 1-indexed start from first block, convert to 0-indexed for line slicing
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

        # Group target_blocks by mutual group
        groups: list[list[TheoremBlock]] = []
        seen = set()
        for block in target_blocks:
            if block.name in seen:
                continue
            if block.mutual_group is not None:
                # Find all target_blocks in same mutual group
                group = [b for b in target_blocks if b.mutual_group == block.mutual_group]
                for b in group:
                    seen.add(b.name)
                groups.append(group)
            else:
                seen.add(block.name)
                groups.append([block])

        # Build dependency map using thm_depends_on
        extracted_name_set = {b.name for b in target_blocks}
        deps_map: dict[str, list[str]] = {}
        for block in target_blocks:
            deps = self.thm_depends_on(file_path, block.name)
            deps_map[block.name] = [d for d in deps if d in extracted_name_set]

        # Merge groups with circular dependencies (SCC on group graph)
        # Build group-level dependency graph
        name_to_group_idx = {}
        for gi, group in enumerate(groups):
            for b in group:
                name_to_group_idx[b.name] = gi

        # Find cycles: if group A depends on group B and B depends on A, merge them
        merged = True
        while merged:
            merged = False
            group_deps: dict[int, set[int]] = {i: set() for i in range(len(groups))}
            # Rebuild name→group mapping
            name_to_group_idx = {}
            for gi, group in enumerate(groups):
                for b in group:
                    name_to_group_idx[b.name] = gi
            # Build group-level deps
            for gi, group in enumerate(groups):
                for b in group:
                    for dep_name in deps_map.get(b.name, []):
                        dep_gi = name_to_group_idx.get(dep_name)
                        if dep_gi is not None and dep_gi != gi:
                            group_deps[gi].add(dep_gi)
            # Find any mutual dependency (cycle of length 2+)
            for gi in range(len(groups)):
                for gj in group_deps.get(gi, set()):
                    if gi in group_deps.get(gj, set()):
                        # Merge gj into gi
                        groups[gi] = groups[gi] + groups[gj]
                        groups.pop(gj)
                        merged = True
                        break
                if merged:
                    break

        # For each group, use the first theorem's name as the file name
        name_to_module: dict[str, str] = {}
        out_rel = str(out_path.relative_to(root))
        for group in groups:
            safe_name = _ascii_escape(group[0].name)
            module = f"{out_rel}/lemma_helper_{safe_name}".replace("/", ".")
            for b in group:
                name_to_module[b.name] = module

        # Extract each group into its own file
        created_files: list[str] = []
        extracted_names: list[str] = []

        for group in groups:
            if len(group) > 1:
                # Mutual group: grab raw lines from file (mutual...end inclusive)
                # Lines are 1-indexed; first member starts at mutual keyword
                first_line = min(b.start for b in group) - 1  # 0-indexed, includes 'mutual'
                last_line = max(b.end for b in group)  # 1-indexed end of last member
                # Find the 'end' line after last member
                end_idx = last_line  # 0-indexed search start
                while end_idx < len(lines) and lines[end_idx].strip() != "end":
                    end_idx += 1
                block_lines = lines[first_line:end_idx + 1]
                # Strip 'private' from all declarations
                block_lines = [l.replace("private theorem ", "theorem ").replace("private def ", "def ").replace("private noncomputable def ", "noncomputable def ")
                               for l in block_lines]
                block_text = "\n".join(block_lines)
            else:
                # Standalone: use the clean text from itp_interface
                block = group[0]
                block_text = block.text
                # Strip 'private'
                block_text = block_text.replace("private theorem ", "theorem ", 1)
                block_text = block_text.replace("private def ", "def ", 1)
                block_text = block_text.replace("private noncomputable def ", "noncomputable def ", 1)

            # Add imports for sibling theorems this group depends on
            group_names = {b.name for b in group}
            dep_imports = set()
            for b in group:
                for dep_name in deps_map.get(b.name, []):
                    if dep_name not in group_names:
                        dep_imports.add(f"import {name_to_module[dep_name]}")

            safe_name = _ascii_escape(group[0].name)
            new_filename = f"lemma_helper_{safe_name}.lean"
            new_path = out_path / new_filename

            # Build file: header + dep imports + block text
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

            rel_path = str(new_path.relative_to(root))
            created_files.append(rel_path)
            extracted_names.extend(b.name for b in group)

        # Build files in dependency order so .olean files exist for sibling imports
        import subprocess
        # Topological sort: build files that have no sibling deps first
        file_to_deps: dict[str, set[str]] = {}
        name_to_file: dict[str, str] = {}
        for f, names in zip(created_files, [extracted_names]):
            pass  # need per-group info

        # Simple approach: build all files, repeat until no progress (handles cycles)
        remaining = list(created_files)
        for _ in range(3):  # max 3 passes
            still_failing = []
            for f in remaining:
                module = f.replace("/", ".").removesuffix(".lean")
                result = subprocess.run(["lake", "build", module],
                    cwd=str(root), capture_output=True, timeout=120)
                if result.returncode != 0:
                    still_failing.append(f)
            if not still_failing:
                break
            remaining = still_failing

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
