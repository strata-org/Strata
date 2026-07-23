"""Start the StrataSwarm v3 dashboard (default port 8421).

    python run_dashboard.py --port 9000           # serve on a different port

Cheat-sheet defaults can be set at launch:
    python run_dashboard.py                       # bundled cheat sheet (default)
    python run_dashboard.py --no-cheat-sheet      # disable the cheat sheet
    python run_dashboard.py --cheat-sheet path/to/Playbook.md   # custom playbook

These set the workflow-wide DEFAULT. A per-request instruction in chat
("no cheat sheet", "use playbook X") still overrides it for that proof.
"""

import argparse
import asyncio
import os
import signal
import sys
from pathlib import Path

# Ensure StrataAgent is importable
sys.path.insert(0, str(Path(__file__).parent.parent))

from strataswarm._claude_backend import ClaudeBackend
from strataswarm._server import SwarmDashboard

DEFAULT_PORT = 8421
PID_FILE = Path(__file__).parent.parent / "temp" / "dashboard.pid"


def kill_stale_process(port: int):
    """Kill any stale dashboard process using our port or PID file."""
    if PID_FILE.exists():
        try:
            old_pid = int(PID_FILE.read_text().strip())
            os.kill(old_pid, signal.SIGTERM)
            print(f"[CLEANUP] Killed stale process {old_pid} from PID file")
            import time
            time.sleep(1)
        except (ProcessLookupError, ValueError, PermissionError):
            pass
        PID_FILE.unlink(missing_ok=True)

    try:
        import subprocess
        result = subprocess.run(
            ["lsof", "-ti", f":{port}"],
            capture_output=True, text=True, timeout=5
        )
        if result.stdout.strip():
            for pid_str in result.stdout.strip().split('\n'):
                try:
                    pid = int(pid_str.strip())
                    if pid != os.getpid():
                        os.kill(pid, signal.SIGTERM)
                        print(f"[CLEANUP] Killed process {pid} holding port {port}")
                        import time
                        time.sleep(1)
                except (ValueError, ProcessLookupError, PermissionError):
                    pass
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Start the StrataSwarm dashboard.")
    p.add_argument("--port", type=int, default=DEFAULT_PORT,
                   help=f"Port to serve the dashboard on (default: {DEFAULT_PORT}).")
    g = p.add_mutually_exclusive_group()
    g.add_argument("--no-cheat-sheet", action="store_true",
                   help="Disable the proof cheat sheet by default.")
    g.add_argument("--cheat-sheet", metavar="PATH", default=None,
                   help="Use a custom cheat-sheet/playbook file instead of the "
                        "bundled one. Resolved to an absolute path (relative to "
                        "the current directory); errors if the file is missing.")
    return p.parse_args()


def _apply_cheat_sheet_env(args: argparse.Namespace) -> None:
    """Publish launch-time cheat-sheet defaults via env for the task manager."""
    if args.no_cheat_sheet:
        os.environ["STRATA_USE_CHEAT_SHEET"] = "0"
        os.environ["STRATA_CHEAT_SHEET_PATH"] = ""
        print("[CONFIG] Cheat sheet DISABLED by default (--no-cheat-sheet)")
    elif args.cheat_sheet:
        # Resolve to an ABSOLUTE path so it survives the dashboard's cwd (the
        # prover resolves cheat_sheet_path against the repo-root cwd, not the
        # invoking shell's). Fail loudly if missing rather than letting the guide
        # later report "cheat sheet inaccessible".
        import pathlib
        p = pathlib.Path(args.cheat_sheet)
        resolved = p.resolve() if p.exists() else (pathlib.Path.cwd() / args.cheat_sheet).resolve()
        if not resolved.is_file():
            raise SystemExit(
                f"ERROR: --cheat-sheet file not found: '{args.cheat_sheet}' "
                f"(resolved to {resolved}; cwd: {pathlib.Path.cwd()}).")
        os.environ["STRATA_USE_CHEAT_SHEET"] = "1"
        os.environ["STRATA_CHEAT_SHEET_PATH"] = str(resolved)
        print(f"[CONFIG] Default cheat sheet: {resolved}")


async def main(args: argparse.Namespace) -> None:
    _apply_cheat_sheet_env(args)
    kill_stale_process(args.port)

    pid = os.getpid()
    PID_FILE.parent.mkdir(parents=True, exist_ok=True)
    PID_FILE.write_text(str(pid))
    print(f"StrataSwarm v3 Dashboard PID: {pid}")

    dashboard = SwarmDashboard(
        backend_factory=ClaudeBackend,
        host="0.0.0.0",
        port=args.port,
    )
    await dashboard.start()
    print(f"Dashboard running at http://localhost:{args.port}")
    print(f"Load 'swarm' from the UI to start the LeanSwarm config.")
    try:
        await asyncio.Event().wait()
    finally:
        PID_FILE.unlink(missing_ok=True)


if __name__ == "__main__":
    asyncio.run(main(_parse_args()))
