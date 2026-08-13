"""Lightweight headless "task manager" for benchmark / batch runs.

This is the no-frills counterpart of ``task_manager``: it drives ONE theorem to a
verdict and exits, with NO ``tm_monitor`` loop and NO ``tm_clarifier`` / human
input — those are pure cost in an unattended benchmark. It keeps exactly the two
things that matter:

  1. dispatch the ``prover_v5`` agent (the real proof engine), awaited to completion;
  2. run the SAME final ``deep_proof_validator`` the full TM runs, as the
     authoritative pass/fail.

Flow (mirrors task_manager's SETUP → DISPATCH → VALIDATE, minus MONITOR/CLARIFIER):
  * copy the target theorem file → ``StrataAgent/Sandbox/Stub.lean`` (the prover
    then snapshots it to ``Stub.clean.lean`` and proves in place);
  * ``prover_v5.run(...)`` — awaited directly (no background monitor task, no
    watchdog); its output carries ``give_up_reason`` / ``user_fix_request``;
  * ``deep_proof_validator.run(...)`` → compiles / has_sorry / statements_match;
  * return a structured result dict the launcher serializes to JSON.

Invoked as a module agent (see agent_specs/agents/headless_prover.yaml) by
``run_headless.py``. The interactive dashboard / full TaskManager are untouched.
"""

from __future__ import annotations

import shutil
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .._types import AgentResult, AgentStatus


async def run_workflow(agent, inp: Any, result_type=None):  # noqa: ARG001
    from .._helpers import swarm_agent

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
    started = time.time()

    if not isinstance(inp, dict):
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"status": "error", "detail": "inp must be a dict"})

    theorem_file = inp.get("theorem_file", "")
    theorem_names = list(inp.get("theorem_names") or [])
    workspace = inp.get("workspace", "StrataAgent/Sandbox")
    if not theorem_file:
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"status": "error", "detail": "theorem_file required"})

    # ── SETUP: copy the target theorem file → Sandbox/Stub.lean ──────────────
    src = cwd / theorem_file
    stub = cwd / workspace / "Stub.lean"
    if not src.exists():
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"status": "error", "detail": f"theorem_file not found: {src}"})
    stub.parent.mkdir(parents=True, exist_ok=True)
    # Clear any stale artifacts from a previous run in this Sandbox.
    for entry in stub.parent.iterdir():
        if entry.name == ".gitkeep":
            continue
        shutil.rmtree(entry, ignore_errors=True) if entry.is_dir() else entry.unlink(missing_ok=True)
    shutil.copy2(src, stub)
    await agent._emit("message", f"[HL] Setup: {theorem_file} → {workspace}/Stub.lean")

    # ── DISPATCH: run the prover directly (no monitor, no watchdog) ──────────
    prover_input = {
        "theorem_file": theorem_file,
        "theorem_names": theorem_names,
        "workspace": workspace,
        "skip_soundness": inp.get("skip_soundness", True),
        "use_cheat_sheet": inp.get("use_cheat_sheet", False),
        "cheat_sheet_path": inp.get("cheat_sheet_path", ""),
        "max_run_minutes": inp.get("max_run_minutes"),
        "parent_agent": agent.spec.name,
    }
    prover_out: dict[str, Any] = {}
    await agent._emit("message", "[HL] Dispatching prover_v5 (headless, no monitor)...")
    try:
        async with swarm_agent("prover_v5", swarm=agent.swarm, cwd=agent._cwd) as prover:
            result = await prover.run(inp=prover_input, result_type=None)
            out = getattr(result, "output", None)
            if isinstance(out, dict):
                prover_out = out
    except Exception as e:  # noqa: BLE001
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"status": "error", "detail": f"prover error: {e}",
                                   "wall_s": round(time.time() - started, 1)})

    give_up_reason = str(prover_out.get("give_up_reason", "") or "")
    user_fix_request = str(prover_out.get("user_fix_request", "") or "")

    # ── VALIDATE: the authoritative deep validation (same as the full TM) ────
    @dataclass
    class _Validation:
        compiles: bool
        has_sorry: bool
        statements_match: bool

    from .._lean_tools_mcp import create_lean_tools_server
    validator_mcp = {"lean_tools": create_lean_tools_server(workspace=None)}
    compiles = has_sorry = stmt_match = None
    await agent._emit("message", "[HL] Deep validation...")
    try:
        async with swarm_agent("deep_proof_validator", swarm=agent.swarm, cwd=agent._cwd,
                               extra_mcp_servers=validator_mcp) as validator:
            v = await validator.run(
                inp={"stub_file": theorem_file, "complete_file": f"{workspace}/Stub.lean"},
                result_type=_Validation)
            vo = getattr(v, "output", None)
            if vo is not None:
                compiles, has_sorry, stmt_match = vo.compiles, vo.has_sorry, vo.statements_match
    except Exception as e:  # noqa: BLE001
        await agent._emit("message", f"[HL] Validator error: {e}")

    proven = bool(compiles) and has_sorry is False and bool(stmt_match)
    status = "proven" if proven else ("give_up" if give_up_reason or user_fix_request else "failed")

    output = {
        "status": status,
        "proven": proven,
        "compiles": compiles,
        "has_sorry": has_sorry,
        "statements_match": stmt_match,
        "give_up_reason": give_up_reason,
        "user_fix_request": user_fix_request,
        "prover_stage": prover_out.get("stage"),
        "wall_s": round(time.time() - started, 1),
        "stub_rel": f"{workspace}/Stub.lean",
    }
    await agent._emit("message", f"[HL] Done: status={status} ({output['wall_s']}s)")
    return AgentResult(name=agent.spec.name,
                       status=AgentStatus.COMPLETED if proven else AgentStatus.FAILED,
                       output=output)
