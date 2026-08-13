#!/usr/bin/env python3
"""Headless single-theorem launcher (no dashboard, no HTTP server, no tm_monitor).

Builds a minimal Swarm and runs the ``headless_prover`` module agent on ONE
theorem: copy target → Sandbox/Stub.lean, dispatch prover_v5, run the deep
validation, then print a single JSON result line to stdout (prefixed
``__HEADLESS_RESULT__``) so a parent process (the benchmark runner) can parse it.

Run inside a project clone (its own repo + StrataAgent/Sandbox):

    StrataAgent/.venv/bin/python StrataAgent/run_headless.py \
        --theorem-file Path/To/File.lean \
        --theorem thm_name \
        [--workspace StrataAgent/Sandbox] \
        [--cheat-sheet PATH] [--max-run-minutes 120] [--json-out result.json]

Emits result JSON with: status (proven|give_up|failed|error), proven, compiles,
has_sorry, statements_match, give_up_reason, user_fix_request, wall_s, stub_rel.
"""

from __future__ import annotations

import argparse
import asyncio
import json
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

RESULT_PREFIX = "__HEADLESS_RESULT__"


def _parse_args(argv):
    ap = argparse.ArgumentParser(description="Headless single-theorem prover launcher")
    ap.add_argument("--theorem-file", required=True,
                    help="target .lean file, relative to the project (lake) root")
    ap.add_argument("--theorem", action="append", default=[],
                    help="theorem name to prove (repeatable). Empty → all sorry-theorems.")
    ap.add_argument("--workspace", default="StrataAgent/Sandbox")
    ap.add_argument("--cheat-sheet", default="")
    ap.add_argument("--max-run-minutes", type=float, default=None)
    ap.add_argument("--json-out", default="", help="also write the result JSON here")
    return ap.parse_args(argv)


async def _run(args) -> dict:
    from strataswarm._swarm import Swarm
    from strataswarm._claude_backend import ClaudeBackend
    from strataswarm._helpers import swarm_agent

    project_root = str(Path.cwd())
    swarm = Swarm(
        backend_factory=ClaudeBackend,
        enable_messaging=True,
        wait_after_completion=False,   # headless: agent completes and returns
        name="HeadlessSwarm",
        cwd=project_root,
        checkpoint_dir=str(_HERE / "strataswarm" / "temp" / "checkpoints"),
    )

    inp = {
        "theorem_file": args.theorem_file,
        "theorem_names": list(args.theorem or []),
        "workspace": args.workspace,
        "use_cheat_sheet": bool(args.cheat_sheet),
        "cheat_sheet_path": args.cheat_sheet or "",
        "max_run_minutes": args.max_run_minutes,
    }
    async with swarm_agent("headless_prover", swarm=swarm, cwd=project_root) as hp:
        result = await hp.run(inp=inp, result_type=None)
    out = getattr(result, "output", None)
    return out if isinstance(out, dict) else {"status": "error", "detail": "no output"}


def main(argv) -> int:
    args = _parse_args(argv)
    try:
        out = asyncio.run(_run(args))
    except Exception as e:  # noqa: BLE001
        out = {"status": "error", "detail": f"{type(e).__name__}: {e}"}
    line = RESULT_PREFIX + json.dumps(out)
    print(line, flush=True)
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(out, indent=2))
    return 0 if out.get("status") == "proven" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
