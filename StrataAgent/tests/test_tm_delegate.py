"""Regression test for TaskManager._delegate message delivery.

Guards the bug where the persistent-mailbox rewrite turned {agent}:messages into
a wakeup SIGNAL (payload=msg_id, content in the mailbox) while _delegate still
routed the user request through that queue's payload and called run_ai(inp=None).
The internal clarifier/chat/monitor agents are auto_start=false with NO background
listen loop, so they never saw the request and answered "no request provided yet".

Fix: _delegate hands the message content to the internal agent directly as
run_ai(inp=...). This test asserts that contract for both the clarifier branch
and the else (chat/monitor) branch.

Run:
  PYTHONPATH=StrataAgent <py> tests/test_tm_delegate.py
"""

from __future__ import annotations

import asyncio
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from strataswarm._types import AgentResult, AgentStatus
from strataswarm.modules import task_manager as tm
from strataswarm.modules.task_manager import (
    WorkflowState, Handler, ClarifierResponse,
)


# ── fakes ─────────────────────────────────────────────────────────────────────

class _FakeChannel:
    def __init__(self):
        self.sent: list[tuple[str, str, object]] = []

    async def send_to(self, channel_name, sender, payload, topic=""):
        self.sent.append((channel_name, sender, payload))


class _FakeSpec:
    def __init__(self, name):
        self.name = name


class _FakeInternalAgent:
    """Records the inp handed to run_ai and returns a canned structured result."""

    def __init__(self, name, canned_output):
        self.spec = _FakeSpec(name)
        self._canned = canned_output
        self.run_ai_inp = "<never called>"

    async def run_ai(self, inp=None, result_type=None, max_turns=None):
        self.run_ai_inp = inp
        res: AgentResult = AgentResult(name=self.spec.name, status=AgentStatus.COMPLETED)
        res.output = self._canned
        res.raw_result = str(self._canned)
        return res


class _FakeAgent:
    def __init__(self):
        self.spec = _FakeSpec("TaskManager")
        self.channel_bus = _FakeChannel()
        self._cwd = "."
        self.messages: list[str] = []

    async def _emit(self, event_type, data=None):
        if event_type == "message":
            self.messages.append(str(data))


# ── tests ──────────────────────────────────────────────────────────────────────

async def test_delegate_clarifier_passes_content_as_inp():
    agent = _FakeAgent()
    internal = _FakeInternalAgent(
        "tm_clarifier_1",
        ClarifierResponse(needs_user_input=True, question_for_user="which file?"),
    )

    # Stub _get_internal_agent so no real agent is spawned.
    orig = tm._get_internal_agent
    async def _fake_get(state, ag, which):
        return internal
    tm._get_internal_agent = _fake_get
    try:
        state = WorkflowState()
        state.sender = "user"
        state.raw_input = "Please prove theorem foo in Bar.lean"
        await tm._delegate(state, agent, Handler.CLARIFIER)
    finally:
        tm._get_internal_agent = orig

    # The message content MUST reach the internal agent via inp — not via the queue.
    assert internal.run_ai_inp is not None, "clarifier got inp=None — the mailbox-rewrite bug"
    assert "Please prove theorem foo in Bar.lean" in internal.run_ai_inp
    assert "user" in internal.run_ai_inp
    print("  test_delegate_clarifier_passes_content_as_inp OK")


async def test_delegate_chat_branch_passes_content_as_inp():
    agent = _FakeAgent()
    internal = _FakeInternalAgent("tm_chat_1", "some chat answer")

    orig = tm._get_internal_agent
    async def _fake_get(state, ag, which):
        return internal
    tm._get_internal_agent = _fake_get
    try:
        state = WorkflowState()
        state.sender = "user"
        state.raw_input = "what does Block.mk do?"
        await tm._delegate(state, agent, Handler.CHAT)
    finally:
        tm._get_internal_agent = orig

    assert internal.run_ai_inp is not None, "chat got inp=None — the mailbox-rewrite bug"
    assert "what does Block.mk do?" in internal.run_ai_inp
    print("  test_delegate_chat_branch_passes_content_as_inp OK")


async def test_delegate_status_check_default_when_no_input():
    """Monitor ticks have empty raw_input; the agent must still get a non-empty inp."""
    agent = _FakeAgent()
    internal = _FakeInternalAgent("tm_monitor_1", "status: ok")

    orig = tm._get_internal_agent
    async def _fake_get(state, ag, which):
        return internal
    tm._get_internal_agent = _fake_get
    try:
        state = WorkflowState()
        state.sender = "system"
        state.raw_input = ""
        await tm._delegate(state, agent, Handler.MONITOR)
    finally:
        tm._get_internal_agent = orig

    assert internal.run_ai_inp is not None and internal.run_ai_inp.strip()
    assert "Status check." in internal.run_ai_inp
    print("  test_delegate_status_check_default_when_no_input OK")


if __name__ == "__main__":
    asyncio.run(test_delegate_clarifier_passes_content_as_inp())
    asyncio.run(test_delegate_chat_branch_passes_content_as_inp())
    asyncio.run(test_delegate_status_check_default_when_no_input())
    print("ALL TM DELEGATE TESTS PASSED")
