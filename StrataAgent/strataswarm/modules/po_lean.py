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
    start: int = 0  # line number (0-indexed)
    end: int = 0
    has_sorry: bool = False


@dataclass
class SplitResult:
    blocks: list[TheoremBlock] = field(default_factory=list)
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
        """Get theorem blocks with line extents and sorry status."""
        result = self._send("split_theorems_", file_path)
        if "error" in result:
            return SplitResult(error=result["error"])
        return SplitResult(
            blocks=[TheoremBlock(name=b["name"], start=b["start"], end=b["end"],
                                 has_sorry=b["has_sorry"])
                    for b in result.get("blocks", [])],
        )

    # ─── Convenience methods ─────────────────────────────────────────────

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

    def extract_sorry_theorems(self, file_path: str, output_dir: str | None = None) -> ExtractResult:
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

        sorry_blocks = [b for b in split.blocks if b.has_sorry]
        if not sorry_blocks:
            return ExtractResult(skipped=True, reason="no sorry theorems")

        content = source.read_text()
        lines = content.splitlines()

        # Header = everything before first theorem (imports, opens, variables)
        first_thm_line = min(b.start for b in split.blocks) if split.blocks else 0
        header = "\n".join(lines[:first_thm_line])

        # Output directory
        if output_dir:
            out_path = root / output_dir
        else:
            out_path = source.parent
        out_path.mkdir(parents=True, exist_ok=True)

        # Extract each sorry theorem into its own file
        created_files: list[str] = []
        extracted_names: list[str] = []

        for block in sorry_blocks:
            block_text = "\n".join(lines[block.start:block.end + 1])
            safe_name = _ascii_escape(block.name)
            new_filename = f"lemma_helper_{safe_name}.lean"
            new_path = out_path / new_filename

            new_content = header.rstrip() + "\n\n" + block_text + "\n"
            new_path.write_text(new_content)

            rel_path = str(new_path.relative_to(root))
            created_files.append(rel_path)
            extracted_names.append(block.name)

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
            created_files = [f for f in created_files if f not in failed_files]
            extracted_names = [n for n, f in zip(extracted_names, created_files)]

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
