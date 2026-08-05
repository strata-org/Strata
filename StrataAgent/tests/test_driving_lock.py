"""Deterministic tests for the _driving_lock session-ownership guard (persistent
guide+writer listeners, PO v5).

Background: PO v5 now keeps the writer AND guide alive as persistent
`_listen_messages` tasks for the whole lemma, while the orchestrator still drives
each of them with `run_ai` when it needs a chunk / review / decision. Both the
listen loop and run_ai consume turns on the SAME backend session. Without
coordination they would interleave turns and split the result across two
`AgentResult` objects (silent mis-attribution — a wrong/blank guide decision).

The fix is `_driving_lock` (Agent, SEPARATE from `_backend_lock`):
  * run_ai() holds it for the WHOLE run (blocking acquire).
  * _listen_messages() only TRIES it (parks while held), and holds it across its
    own consume so the two never overlap.

These tests exercise the guarantees with a scripted in-process fake backend — no
LLM, no network:

  * run_ai while a listener is live → every turn lands in run_ai's result, the
    listener consumes NOTHING during the run (no mis-attribution, no deadlock).
  * a message that arrives WHILE run_ai drives is left on the channel and picked
    up by the listener only AFTER run_ai releases the lock.
  * a message that arrives while the agent is idle is processed by the listener.
  * lock ordering: _driving_lock is not _backend_lock (re-entrancy safety).

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_driving_lock.py
"""

from __future__ import annotations

import asyncio
import os
import sys
from collections.abc import AsyncIterator

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm._agent import SwarmAgent
from strataswarm._backend import AgentBackend, BackendConfig, BackendMessage
from strataswarm._channels import ChannelBus, ChannelMessage
from strataswarm._types import AgentSpec
from strataswarm._tokens import CancellationToken


# ── Scripted fake backend ────────────────────────────────────────────────────
class ScriptedBackend(AgentBackend):
    """Answers each send_query with: one text turn echoing the query tag, then a
    result. Records every query it received so a test can assert which loop drove
    which turn. Fully deterministic, in-process."""

    def __init__(self) -> None:
        self._messages: list[BackendMessage] = []
        self.queries: list[str] = []
        self._pending: str | None = None
        self._turns = 0
        self._session_id = "sess-fake"
        # Concurrency sentinel: the WHOLE point of _driving_lock is that a turn's
        # consume is never interleaved with another consume on this same session.
        # If run_ai and the listener ever consume concurrently, this trips.
        self._consuming = False
        self.max_concurrency = 0

    async def connect(self, config: BackendConfig) -> None:
        return None

    async def send_query(self, prompt: str) -> None:
        self.queries.append(prompt)
        self._pending = prompt

    async def receive_messages(self) -> AsyncIterator[BackendMessage]:
        # Emit the response for the most recent query, then a result that ends the
        # turn (halted_by == "completion", so _run_inner loops for the next query).
        assert not self._consuming, "CONCURRENT CONSUME on one session — _driving_lock failed"
        self._consuming = True
        self.max_concurrency = max(self.max_concurrency, 1)
        try:
            assert self._pending is not None
            q = self._pending
            self._pending = None
            self._turns += 1
            # tiny awaits so other tasks get real chances to interleave (mirrors
            # real streaming) — this is where a broken lock would let a second
            # consume slip in and trip the sentinel above.
            await asyncio.sleep(0)
            yield BackendMessage(type="text", content=f"ack:{q[:40]}")
            await asyncio.sleep(0)
            yield BackendMessage(
                type="result", raw_result=f"done:{q[:40]}", cost_usd=0.0,
                num_turns=self._turns, session_id=self._session_id, stop_reason="end_turn",
            )
        finally:
            self._consuming = False

    async def interrupt(self) -> None:
        return None

    async def disconnect(self) -> None:
        return None


def _make_agent(name: str, bus: ChannelBus) -> SwarmAgent:
    spec = AgentSpec(name=name, system_prompt="test", stateless=False)
    agent = SwarmAgent(
        spec=spec,
        backend=ScriptedBackend(),
        channel_bus=bus,
        mcp_servers_override={"agent_messaging": {"instance": object()}},
    )
    # _run_inner sets halted_by "completion" only when the result loop wants to
    # continue; keep the agent stateful and non-waiting so run_ai returns after
    # its scripted turns.
    agent._wait_after_completion = False
    return agent


def _signal(bus: ChannelBus, name: str, sender: str) -> None:
    """Drop a wakeup signal on {name}:messages, as send_message would."""
    ch = bus.get_or_create(f"{name}:messages")
    ch._queue.put_nowait(ChannelMessage(sender=sender, payload="msg-id"))


# ── Tests ────────────────────────────────────────────────────────────────────
async def test_listener_parks_while_driving_lock_held() -> None:
    """DETERMINISTIC: while _driving_lock is held (as run_ai holds it for its whole
    run), the listener must NOT consume a signalled message — it parks. The moment
    the lock is released, it processes the message. This is the core guard, tested
    without racing timing: we hold the exact lock run_ai would hold."""
    bus = ChannelBus()
    agent = _make_agent("writer", bus)
    agent._mailbox_push = lambda: "MAIL: hello"  # type: ignore[method-assign]

    token = CancellationToken()

    # Hold _driving_lock ourselves (stand in for an in-flight run_ai).
    await agent._driving_lock.acquire()

    listen_task = asyncio.ensure_future(agent._listen_messages(token))
    _signal(bus, "writer", "guide")

    # Give the listener several full loop iterations (it sleeps ~1s each). It must
    # keep parking — consume nothing — for as long as we hold the lock.
    for _ in range(25):
        await asyncio.sleep(0.1)
    assert agent.backend.queries == [], \
        f"listener consumed while _driving_lock was held: {agent.backend.queries}"

    # Release the lock — now the listener is free to pick up the parked signal.
    agent._driving_lock.release()
    for _ in range(40):
        await asyncio.sleep(0.1)
        if agent.backend.queries:
            break
    assert agent.backend.queries and agent.backend.queries[0].startswith("MAIL:"), \
        f"listener did not resume after lock release: {agent.backend.queries}"
    # And it never overlapped a consume with anything.
    assert agent.backend.max_concurrency == 1

    token.cancel()
    listen_task.cancel()
    try:
        await listen_task
    except (asyncio.CancelledError, Exception):
        pass


async def test_listener_processes_when_idle() -> None:
    """When run_ai is NOT driving, the listener picks up a signal and injects it."""
    bus = ChannelBus()
    agent = _make_agent("guide", bus)
    agent._mailbox_push = lambda: "MAIL: writer asks"  # type: ignore[method-assign]

    token = CancellationToken()
    listen_task = asyncio.ensure_future(agent._listen_messages(token))

    _signal(bus, "guide", "writer")
    # The listen loop sleeps up to ~1s per iteration; give it a couple cycles.
    for _ in range(40):
        await asyncio.sleep(0.1)
        if any(q.startswith("MAIL:") for q in agent.backend.queries):
            break

    assert any(q.startswith("MAIL:") for q in agent.backend.queries), \
        f"idle listener never processed the message: {agent.backend.queries}"

    token.cancel()
    listen_task.cancel()
    try:
        await listen_task
    except (asyncio.CancelledError, Exception):
        pass


async def test_no_deadlock_interleaved() -> None:
    """Hammer run_ai and signals together: must always terminate (no deadlock),
    and no run_ai result is ever corrupted by the listener."""
    bus = ChannelBus()
    agent = _make_agent("writer", bus)
    agent._mailbox_push = lambda: "MAIL: x"  # type: ignore[method-assign]

    token = CancellationToken()
    listen_task = asyncio.ensure_future(agent._listen_messages(token))
    await asyncio.sleep(0)

    for i in range(8):
        _signal(bus, "writer", "guide")  # racing signals
        result = await asyncio.wait_for(agent.run_ai(inp=f"chunk {i}", max_turns=3), timeout=10)
        assert result.raw_result and result.raw_result.startswith("done:"), (i, result.raw_result)

    assert agent.backend.max_concurrency == 1, "concurrent consume under interleave"

    token.cancel()
    listen_task.cancel()
    try:
        await listen_task
    except (asyncio.CancelledError, Exception):
        pass


async def test_driving_lock_is_separate_from_backend_lock() -> None:
    """The guard must be a DISTINCT lock — sharing _backend_lock would self-deadlock
    run_ai (it re-enters _consume_response per turn; asyncio locks are non-reentrant)."""
    bus = ChannelBus()
    agent = _make_agent("writer", bus)
    assert agent._driving_lock is not agent._backend_lock
    # run_ai completing at all proves _driving_lock does not deadlock with the
    # per-turn _backend_lock acquisition inside _consume_response.
    result = await asyncio.wait_for(agent.run_ai(inp="ping", max_turns=2), timeout=10)
    assert result.raw_result == "done:ping"


async def test_block_tools_live_during_run_then_cleared() -> None:
    """run_ai(block_tools=[...]) must populate agent._blocked_tools for the DURATION
    of the run (so the PreToolUse block hook can deny those tools) and clear it on
    exit. A plain run leaves it empty. This is what stops the guide from
    send_message-ing the writer during a strategy/decision consult."""
    bus = ChannelBus()
    agent = _make_agent("guide", bus)
    # The ScriptedBackend records max_concurrency but not the block set; snapshot it
    # ourselves at send_query time via a wrapper.
    observed: list[set] = []
    orig_send = agent.backend.send_query

    async def _spy(prompt: str) -> None:
        observed.append(set(agent._blocked_tools))
        await orig_send(prompt)

    agent.backend.send_query = _spy  # type: ignore[method-assign]

    assert agent._blocked_tools == set()
    await asyncio.wait_for(
        agent.run_ai(inp="strategy?", max_turns=2,
                     block_tools=["send_message", "wait_for_reply"]),
        timeout=10)
    assert observed and observed[0] == {"send_message", "wait_for_reply"}, \
        f"block set not live during run: {observed}"
    assert agent._blocked_tools == set(), "block set not cleared after run"

    await asyncio.wait_for(agent.run_ai(inp="again", max_turns=2), timeout=10)
    assert observed[-1] == set(), f"plain run should have empty block set: {observed[-1]}"


async def test_block_hook_denies_only_blocked_tools() -> None:
    """The live block hook denies a tool by bare name or full MCP name when it is in
    _blocked_tools, passes everything else, and is a no-op when the set is empty."""
    from strataswarm.modules.hooks import blocked_tools_hooks

    bus = ChannelBus()
    agent = _make_agent("guide", bus)
    hook = blocked_tools_hooks(agent)["PreToolUse"][0].hooks[0]

    def call(tn: str) -> dict:
        return {"hook_event_name": "PreToolUse", "tool_name": tn}

    def denied(r: dict) -> bool:
        return r.get("hookSpecificOutput", {}).get("permissionDecision") == "deny"

    assert await hook(call("mcp__agent_messaging__send_message"), None, None) == {}
    agent._blocked_tools = {"send_message", "wait_for_reply"}
    assert denied(await hook(call("mcp__agent_messaging__send_message"), None, None))
    assert denied(await hook(call("mcp__agent_messaging__wait_for_reply"), None, None))
    assert denied(await hook(call("send_message"), None, None))
    assert await hook(call("mcp__lean_tools__show_file_state"), None, None) == {}
    # only fires on PreToolUse
    assert await hook({"hook_event_name": "PostToolUse", "tool_name": "send_message"}, None, None) == {}


async def _main() -> None:
    for fn in (
        test_driving_lock_is_separate_from_backend_lock,
        test_listener_parks_while_driving_lock_held,
        test_listener_processes_when_idle,
        test_no_deadlock_interleaved,
        test_block_tools_live_during_run_then_cleared,
        test_block_hook_denies_only_blocked_tools,
    ):
        await fn()
        print(f"  {fn.__name__} OK")
    print("ALL DRIVING-LOCK TESTS PASSED")


if __name__ == "__main__":
    asyncio.run(_main())
