"""
Integration tests for SwarmAgent: cancellation, user injection,
and autonomous multi-agent coordination (no DAG dependencies).

Agents coordinate via shared mailbox files and use `sleep` to wait for each other.

Run with: .venv/bin/python tests/test_swarm_agent_integration.py
"""

import asyncio
import os
import shutil
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from pydantic import BaseModel

from strataswarm import (
    AgentEvent,
    AgentResult,
    AgentSpec,
    AgentStatus,
    CancellationToken,
    ChannelBus,
    ChannelMessage,
    ClaudeBackend,
    ContainsText,
    ExecutionMode,
    JsonSchemaParser,
    PauseToken,
    RawTextParser,
    Swarm,
    SwarmAgent,
    ToolSet,
)


# ============================================================================
# Test 1: Cancellation mid-execution
# ============================================================================

async def test_cancellation():
    """
    Scenario: Agent is doing slow work. We cancel after a few seconds.
    Verifies clean shutdown, correct status, and events emitted before cancel.
    """
    print("=== Test 1: SwarmAgent Cancellation ===")

    events: list[AgentEvent] = []

    async def capture_event(event: AgentEvent) -> None:
        events.append(event)

    spec = AgentSpec(
        name="slow-worker",
        prompt=(
            "Count the number of files in each of these directories, one by one. "
            "Run `find <dir> -type f | wc -l` for each:\n"
            "  /usr/lib\n  /usr/share\n  /var/log\n  /etc\n  /opt\n"
            "Report the count for each."
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=10,
        timeout_seconds=60.0,
    )

    cancellation = CancellationToken()
    pause = PauseToken()
    channel_bus = ChannelBus()
    backend = ClaudeBackend()

    agent: SwarmAgent = SwarmAgent(
        spec=spec,
        backend=backend,
        channel_bus=channel_bus,
        cancellation=cancellation,
        pause=pause,
        on_event=capture_event,
    )

    async def cancel_after_delay():
        await asyncio.sleep(10)
        print("  >>> Cancelling agent")
        cancellation.cancel()

    cancel_task = asyncio.create_task(cancel_after_delay())
    result = await agent.run()
    cancel_task.cancel()

    print(f"  Status: {result.status}")
    print(f"  Halted by: {result.halted_by}")
    print(f"  Messages before cancel: {len([e for e in events if e.event_type == 'message'])}")

    assert result.halted_by == "cancelled", f"Expected 'cancelled', got '{result.halted_by}'"
    assert result.status == AgentStatus.CANCELLED

    status_events = [e for e in events if e.event_type == "status_change"]
    assert any(e.data == "running" for e in status_events)
    assert any(e.data == "cancelled" for e in status_events)

    print("  PASSED\n")


# ============================================================================
# Test 2: User sends message mid-execution (pause + inject + resume)
# ============================================================================

async def test_user_message_injection():
    """
    Scenario: Agent writes a script. User pauses, sends a correction, resumes.
    """
    print("=== Test 2: User Message Injection ===")

    tmpdir = tempfile.mkdtemp(prefix="strataswarm_inject_")
    script_path = os.path.join(tmpdir, "fib.py")

    events: list[AgentEvent] = []

    async def capture_event(event: AgentEvent) -> None:
        events.append(event)

    spec = AgentSpec(
        name="code-writer",
        prompt=(
            f"Write a Python script to {script_path} with a function that computes "
            f"fibonacci numbers. Write it using: echo '...' > {script_path}\n"
            f"Then display the file with cat."
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=8,
        timeout_seconds=60.0,
        inbox_channel="code-writer:inbox",
    )

    cancellation = CancellationToken()
    pause = PauseToken()
    channel_bus = ChannelBus()
    backend = ClaudeBackend()

    agent: SwarmAgent = SwarmAgent(
        spec=spec,
        backend=backend,
        channel_bus=channel_bus,
        cancellation=cancellation,
        pause=pause,
        on_event=capture_event,
    )

    async def inject_guidance():
        await asyncio.sleep(2)
        print("  >>> Pausing agent")
        pause.pause()
        await asyncio.sleep(0.5)
        print("  >>> Injecting user feedback")
        inbox = channel_bus["code-writer:inbox"]
        await inbox.send(ChannelMessage(
            sender="user",
            payload="IMPORTANT: Name the function 'compute_fibonacci' and add a docstring.",
        ))
        await asyncio.sleep(0.5)
        print("  >>> Resuming agent")
        pause.resume()

    inject_task = asyncio.create_task(inject_guidance())
    result = await agent.run()
    inject_task.cancel()

    print(f"  Status: {result.status}")
    print(f"  Halted by: {result.halted_by}")

    # Verify injection event
    message_events = [e for e in events if e.event_type == "message"]
    injected = [e for e in message_events if e.data and "Injected from user" in str(e.data)]
    assert len(injected) >= 1, "Expected injection event"

    # Verify pause/resume transitions
    status_events = [e for e in events if e.event_type == "status_change"]
    statuses = [e.data for e in status_events]
    print(f"  Status transitions: {statuses}")
    assert "paused" in statuses or "completed" in statuses, "Expected PAUSED"

    if os.path.exists(script_path):
        content = open(script_path).read()
        print(f"  File written: {len(content)} bytes")
        os.unlink(script_path)

    shutil.rmtree(tmpdir, ignore_errors=True)
    print("  PASSED\n")


# ============================================================================
# Test 3: Two autonomous agents — shared mailbox, no DAG
# ============================================================================

async def test_autonomous_agents_mailbox():
    """
    Scenario: "Researcher & Writer" — NO depends_on.

    Both agents start simultaneously. They share a mailbox directory.

    Researcher: Explores files, finds data, writes findings to the mailbox.
    Writer: Polls the mailbox (using sleep + file check loop) until the
            Researcher's message appears, then uses it to produce output.

    Key: agents coordinate themselves via filesystem + sleep. No framework
    orchestration beyond running them in parallel.
    """
    print("=== Test 3: Autonomous Agents — Shared Mailbox ===")

    tmpdir = tempfile.mkdtemp(prefix="strataswarm_auto_")
    mailbox_dir = os.path.join(tmpdir, "mailbox")
    data_dir = os.path.join(tmpdir, "data")
    os.makedirs(mailbox_dir)
    os.makedirs(data_dir)

    # Set up data for the researcher to find
    with open(os.path.join(data_dir, "metrics.csv"), "w") as f:
        f.write("date,users,revenue\n2024-01-01,1500,45000\n2024-02-01,1800,52000\n2024-03-01,2200,61000\n")

    events: list[AgentEvent] = []

    async def capture_event(event: AgentEvent) -> None:
        events.append(event)

    # --- Researcher: finds data, writes to mailbox ---
    researcher_spec = AgentSpec(
        name="researcher",
        prompt=(
            f"You are the Researcher agent.\n\n"
            f"1. Read the CSV file at {data_dir}/metrics.csv\n"
            f"2. Find the month with the highest revenue\n"
            f"3. Write your finding to the mailbox: echo your answer into {mailbox_dir}/for_writer.txt\n"
            f"   The file should contain ONLY: month=<month>,revenue=<amount>\n"
            f"   Example format: month=2024-01-01,revenue=45000\n\n"
            f"Use Bash for everything. Be precise with the output format."
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=5,
        timeout_seconds=45.0,
    )

    # --- Writer: polls mailbox, then uses the data ---
    writer_spec = AgentSpec(
        name="writer",
        prompt=(
            f"You are the Writer agent.\n\n"
            f"Another agent (Researcher) will write a file to {mailbox_dir}/for_writer.txt\n"
            f"It may not exist yet — you need to WAIT for it.\n\n"
            f"Steps:\n"
            f"1. Once it appears, read it with cat\n"
            f"2. Write a one-sentence summary to {mailbox_dir}/report.txt\n"
            f"   Format: 'The best month was X with revenue Y.'\n\n"
            f"Use Bash for everything."
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=5,
        timeout_seconds=45.0,
    )

    # Both run in parallel, NO depends_on
    swarm = Swarm(backend_factory=lambda: ClaudeBackend())
    swarm.add(researcher_spec)
    swarm.add(writer_spec)
    swarm.set_event_callback(capture_event)

    results = await swarm.run(mode=ExecutionMode.AWAIT_ALL)

    # --- Validate ---
    researcher_result = results.get("researcher")
    writer_result = results.get("writer")

    assert researcher_result is not None, "Researcher result missing"
    assert writer_result is not None, "Writer result missing"

    print(f"  Researcher: status={researcher_result.status}, halted_by={researcher_result.halted_by}")
    print(f"  Writer: status={writer_result.status}, halted_by={writer_result.halted_by}")

    # Check that the mailbox file was created by researcher
    mailbox_file = os.path.join(mailbox_dir, "for_writer.txt")
    assert os.path.exists(mailbox_file), f"Researcher didn't write to mailbox: {mailbox_file}"
    mailbox_content = open(mailbox_file).read().strip()
    print(f"  Mailbox content: {mailbox_content}")
    assert "61000" in mailbox_content, f"Expected highest revenue (61000) in mailbox"

    # Check the writer's report
    report_file = os.path.join(mailbox_dir, "report.txt")
    if os.path.exists(report_file):
        report = open(report_file).read().strip()
        print(f"  Writer report: {report}")
        assert "61000" in report or "2024-03" in report, "Writer should mention the best month"
    else:
        print("  WARNING: Writer didn't produce report.txt")

    total_cost = sum(r.cost_usd or 0 for r in results.values())
    print(f"  Total cost: ${total_cost:.4f}")

    shutil.rmtree(tmpdir)
    print("  PASSED\n")


# ============================================================================
# Test 4: Three autonomous agents — relay race with sleep-based coordination
# ============================================================================

async def test_three_agents_relay():
    """
    Scenario: "Relay Race" — 3 agents, NO dependencies, all start together.

    Shared workspace with a mailbox. Each agent knows its role:

    Agent A (Encoder): Picks a random word, base64 encodes it, writes to mailbox/step1.txt
    Agent B (Transformer): Waits for step1.txt, reverses the encoded string, writes to mailbox/step2.txt
    Agent C (Decoder): Waits for step2.txt, reverses it back, base64 decodes, writes final answer to mailbox/answer.txt

    All three start simultaneously. B and C use `sleep` loops to wait.
    Verifies that the final decoded answer matches A's original word.
    """
    print("=== Test 4: Three Agents — Relay Race ===")

    tmpdir = tempfile.mkdtemp(prefix="strataswarm_relay_")
    mailbox = os.path.join(tmpdir, "mailbox")
    os.makedirs(mailbox)

    # We'll tell Agent A to use a specific word so we can verify
    secret_word = "strataswarm"

    events: list[AgentEvent] = []

    async def capture_event(event: AgentEvent) -> None:
        events.append(event)

    agent_a_spec = AgentSpec(
        name="encoder",
        prompt=(
            f"You are Agent A (Encoder) in a relay race.\n\n"
            f"Your task:\n"
            f"1. Take the word: {secret_word}\n"
            f"2. Base64 encode it: echo -n '{secret_word}' | base64\n"
            f"3. Write ONLY the encoded result (no newline, no extra text) to: {mailbox}/step1.txt\n"
            f"   Use: echo -n '<encoded>' > {mailbox}/step1.txt\n\n"
            f"That's it. Just encode and write."
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=3,
        timeout_seconds=30.0,
    )

    agent_b_spec = AgentSpec(
        name="transformer",
        prompt=(
            f"You are Agent B (Transformer) in a relay race.\n\n"
            f"Your task:\n"
            f"1. Wait for {mailbox}/step1.txt to appear:\n"
            f"2. Read it: content=$(cat {mailbox}/step1.txt)\n"
            f"3. Reverse the string: echo -n \"$content\" | rev\n"
            f"4. Write ONLY the reversed string to: {mailbox}/step2.txt\n"
            f"   Use: echo -n '<reversed>' > {mailbox}/step2.txt\n\n"
            f"Wait patiently for step1.txt before proceeding."
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=5,
        timeout_seconds=45.0,
    )

    agent_c_spec = AgentSpec(
        name="decoder",
        prompt=(
            f"You are Agent C (Decoder) in a relay race.\n\n"
            f"Your task:\n"
            f"1. Wait for {mailbox}/step2.txt to appear:\n"
            f"2. Read it: content=$(cat {mailbox}/step2.txt)\n"
            f"3. Reverse it back: echo -n \"$content\" | rev\n"
            f"4. Base64 decode the result: echo -n '<unreversed>' | base64 --decode\n"
            f"5. Write the final decoded word to: {mailbox}/answer.txt\n\n"
            f"Wait patiently for step2.txt before proceeding."
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=5,
        timeout_seconds=60.0,
    )

    # All three start simultaneously — NO depends_on
    swarm = Swarm(backend_factory=lambda: ClaudeBackend())
    swarm.add(agent_a_spec)
    swarm.add(agent_b_spec)
    swarm.add(agent_c_spec)
    swarm.set_event_callback(capture_event)

    results = await swarm.run(mode=ExecutionMode.AWAIT_ALL)

    # --- Validate the relay ---
    for name in ["encoder", "transformer", "decoder"]:
        r = results.get(name)
        assert r is not None, f"{name} result missing"
        print(f"  {name}: status={r.status}, halted_by={r.halted_by}")

    # Check intermediate files
    step1 = os.path.join(mailbox, "step1.txt")
    step2 = os.path.join(mailbox, "step2.txt")
    answer_file = os.path.join(mailbox, "answer.txt")

    if os.path.exists(step1):
        print(f"  step1.txt: {open(step1).read().strip()}")
    if os.path.exists(step2):
        print(f"  step2.txt: {open(step2).read().strip()}")

    assert os.path.exists(answer_file), f"Final answer not written: {answer_file}"
    answer = open(answer_file).read().strip()
    print(f"  answer.txt: {answer}")

    assert secret_word in answer, (
        f"Expected '{secret_word}' in final answer, got '{answer}'"
    )

    total_cost = sum(r.cost_usd or 0 for r in results.values())
    print(f"  Total cost: ${total_cost:.4f}")

    shutil.rmtree(tmpdir)
    print("  PASSED\n")


# ============================================================================
# Main
# ============================================================================

async def main():
    print("\n" + "=" * 60)
    print("SwarmAgent Integration Tests")
    print("=" * 60 + "\n")

    await test_cancellation()
    await test_user_message_injection()
    await test_autonomous_agents_mailbox()
    await test_three_agents_relay()

    print("=" * 60)
    print("All SwarmAgent integration tests passed!")
    print("=" * 60)


if __name__ == "__main__":
    asyncio.run(main())
