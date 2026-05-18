"""
Integration test for ClaudeBackend: multi-turn query + tool use chaining.

This test simulates a simple interaction game:
1. Ask the agent to create a temp file with a secret number
2. Ask it to read the file back and tell us the number
3. Verify the final answer matches

Requires: Claude CLI installed and accessible.
Run with: .venv/bin/python tests/test_claude_backend_integration.py
"""

import asyncio
import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from pydantic import BaseModel, TypeAdapter
from strataswarm import ClaudeBackend, BackendConfig, BackendMessage


async def test_single_query_with_tool_use():
    """Test: send one query that requires Bash tool use, collect all messages."""
    print("=== Test 1: Single query with tool use ===")

    backend = ClaudeBackend()
    config = BackendConfig(
        allowed_tools=["Bash"],
        permission_mode="auto",
        max_turns=3,
    )

    await backend.connect(config)
    await backend.send_query("Run `echo 'strataswarm_test_42'` and tell me the output.")

    messages: list[BackendMessage] = []
    async for msg in backend.receive_messages():
        messages.append(msg)
        print(f"  [{msg.type}] {msg.content or msg.raw_result or '':.80}")

    await backend.disconnect()

    # Verify we got messages
    assert len(messages) > 0, "Expected at least one message"

    # Should have a result at the end
    result_msgs = [m for m in messages if m.type == "result"]
    assert len(result_msgs) == 1, f"Expected 1 result, got {len(result_msgs)}"

    result = result_msgs[0]
    assert result.raw_result is not None, "Expected non-empty raw_result"
    assert "42" in result.raw_result, f"Expected '42' in result: {result.raw_result}"

    # Should have used the Bash tool
    tool_msgs = [m for m in messages if m.type == "tool_use"]
    assert len(tool_msgs) >= 1, "Expected at least one tool_use message"

    print(f"  Result: {result.raw_result[:100]}")
    print(f"  Cost: ${result.cost_usd:.4f}" if result.cost_usd else "  Cost: N/A")
    print("  PASSED\n")


async def test_multi_turn_chaining():
    """
    Test: chain two queries on the same connection.

    Turn 1: Agent writes a secret to a temp file.
    Turn 2: Agent reads the file and reports the secret.

    This exercises the send_query -> receive_messages -> send_query -> receive_messages loop
    that SwarmAgent uses for mid-turn injection.
    """
    print("=== Test 2: Multi-turn query chaining ===")

    secret = "STRATA_SECRET_7891"
    tmpdir = tempfile.mkdtemp(prefix="strataswarm_test_")
    filepath = os.path.join(tmpdir, "secret.txt")

    backend = ClaudeBackend()
    config = BackendConfig(
        allowed_tools=["Bash"],
        permission_mode="auto",
        max_turns=3,
    )

    await backend.connect(config)

    # --- Turn 1: Write the secret ---
    print(f"  Turn 1: Writing secret to {filepath}")
    await backend.send_query(
        f"Run this exact command: echo '{secret}' > {filepath}\n"
        f"Then confirm you wrote it."
    )

    turn1_messages: list[BackendMessage] = []
    async for msg in backend.receive_messages():
        turn1_messages.append(msg)
        print(f"    [{msg.type}] {(msg.content or msg.raw_result or '')[:80]}")

    # Verify file was created
    assert os.path.exists(filepath), f"File not created: {filepath}"
    content = open(filepath).read().strip()
    assert content == secret, f"File content mismatch: {content!r} != {secret!r}"
    print(f"  File verified: {filepath} contains '{secret}'")

    # --- Turn 2: Read it back ---
    print(f"  Turn 2: Asking agent to read the file back")
    await backend.send_query(
        f"Read the file at {filepath} using `cat` and tell me the exact content. "
        f"Reply with ONLY the content, nothing else."
    )

    turn2_messages: list[BackendMessage] = []
    async for msg in backend.receive_messages():
        turn2_messages.append(msg)
        print(f"    [{msg.type}] {(msg.content or msg.raw_result or '')[:80]}")

    await backend.disconnect()

    # Verify turn 2 result contains the secret
    turn2_results = [m for m in turn2_messages if m.type == "result"]
    assert len(turn2_results) == 1, f"Expected 1 result in turn 2, got {len(turn2_results)}"
    assert secret in (turn2_results[0].raw_result or ""), (
        f"Secret not found in turn 2 result: {turn2_results[0].raw_result}"
    )

    # Cleanup
    os.unlink(filepath)
    os.rmdir(tmpdir)

    total_cost = sum(
        (m.cost_usd or 0)
        for m in turn1_messages + turn2_messages
        if m.type == "result"
    )
    print(f"  Total cost: ${total_cost:.4f}")
    print("  PASSED\n")


async def test_interrupt():
    """Test: start a long-running query and interrupt it."""
    print("=== Test 3: Interrupt ===")

    backend = ClaudeBackend()
    config = BackendConfig(
        allowed_tools=["Bash"],
        permission_mode="auto",
        max_turns=10,
    )

    await backend.connect(config)
    await backend.send_query(
        "Count from 1 to 100, running `echo <number>` for each one. Do all 100."
    )

    messages: list[BackendMessage] = []
    interrupted = False
    async for msg in backend.receive_messages():
        messages.append(msg)
        print(f"  [{msg.type}] {(msg.content or msg.raw_result or '')[:60]}")
        # Interrupt after receiving 3 messages
        if len(messages) >= 3 and not interrupted:
            print("  >>> Sending interrupt")
            await backend.interrupt()
            interrupted = True

    await backend.disconnect()

    assert interrupted, "Should have triggered interrupt"
    # The agent should have stopped before completing all 100
    result_msgs = [m for m in messages if m.type == "result"]
    if result_msgs:
        r = result_msgs[0]
        print(f"  Stopped after {r.num_turns} turns, cost: ${r.cost_usd:.4f}" if r.cost_usd else "")

    print("  PASSED\n")


async def test_structured_output_treasure_hunt():
    """
    Test: structured JSON output via Pydantic schema.

    Game: A simple treasure hunt environment. The agent is told there are 3 rooms
    with items hidden in them. It must use Bash to "explore" (cat files we set up),
    figure out where the treasure is, and return a structured answer.
    """
    print("=== Test 4: Structured output — Treasure Hunt ===")

    # --- Pydantic model for the answer ---
    class TreasureAnswer(BaseModel):
        treasure_room: str
        treasure_item: str
        rooms_explored: list[str]
        confidence: float

    # --- Set up the game environment ---
    tmpdir = tempfile.mkdtemp(prefix="strataswarm_treasure_")
    rooms = {
        "cave": "You find: cobwebs, a rusty key, and darkness.",
        "forest": "You find: tall trees, birdsong, and a golden chalice hidden under leaves.",
        "lake": "You find: still water, fish, and smooth pebbles.",
    }
    for room_name, description in rooms.items():
        with open(os.path.join(tmpdir, f"{room_name}.txt"), "w") as f:
            f.write(description)

    system_prompt = f"""You are playing a treasure hunt game.

There are 3 rooms: cave, forest, lake.
Each room has a description file at: {tmpdir}/<room_name>.txt

Rules:
- Explore rooms by running: cat {tmpdir}/<room_name>.txt
- Exactly ONE room contains a treasure (a valuable item).
- You must explore the rooms to find the treasure.
- After exploring, report your findings as structured JSON."""

    # --- Build output_format from Pydantic schema ---
    adapter = TypeAdapter(TreasureAnswer)
    output_format = {"type": "json_schema", "schema": adapter.json_schema()}

    backend = ClaudeBackend()
    config = BackendConfig(
        allowed_tools=["Bash"],
        permission_mode="auto",
        max_turns=5,
        system_prompt=system_prompt,
        output_format=output_format,
    )

    await backend.connect(config)
    await backend.send_query(
        "Explore all 3 rooms (cave, forest, lake) and find the treasure. "
        "Report which room has the treasure and what the item is."
    )

    messages: list[BackendMessage] = []
    async for msg in backend.receive_messages():
        messages.append(msg)
        display = (msg.content or msg.raw_result or str(msg.structured_output) or "")[:80]
        print(f"  [{msg.type}] {display}")

    await backend.disconnect()

    # --- Validate the structured result ---
    result_msgs = [m for m in messages if m.type == "result"]
    assert len(result_msgs) == 1, f"Expected 1 result, got {len(result_msgs)}"

    result = result_msgs[0]
    assert result.structured_output is not None or result.raw_result is not None, (
        "Expected structured_output or raw_result"
    )

    # Parse into Pydantic model
    if result.structured_output:
        answer = adapter.validate_python(result.structured_output)
    else:
        answer = adapter.validate_json(result.raw_result)

    print(f"  Parsed answer: {answer}")

    # Verify correctness
    assert answer.treasure_room == "forest", f"Expected 'forest', got '{answer.treasure_room}'"
    assert "chalice" in answer.treasure_item.lower(), (
        f"Expected 'chalice' in treasure_item, got '{answer.treasure_item}'"
    )
    assert len(answer.rooms_explored) >= 1, "Expected at least 1 room explored"
    assert 0.0 <= answer.confidence <= 1.0, f"Confidence out of range: {answer.confidence}"

    # Should have used Bash to explore
    tool_msgs = [m for m in messages if m.type == "tool_use"]
    assert len(tool_msgs) >= 1, "Expected tool use for exploring rooms"

    # Cleanup
    for room_name in rooms:
        os.unlink(os.path.join(tmpdir, f"{room_name}.txt"))
    os.rmdir(tmpdir)

    print(f"  Cost: ${result.cost_usd:.4f}" if result.cost_usd else "  Cost: N/A")
    print("  PASSED\n")


async def test_structured_output_math_puzzle():
    """
    Test: structured output with a simple computation game.

    Game: The agent is given a "calculator environment" where it must run
    arithmetic commands via Bash to solve a puzzle, then report the answer
    as a structured object.
    """
    print("=== Test 5: Structured output — Math Puzzle ===")

    class MathAnswer(BaseModel):
        expression: str
        result: int
        steps: list[str]

    system_prompt = """You are a math puzzle solver.

You have access to a calculator via Bash: run `echo $((expression))` to evaluate.

Solve the puzzle by computing intermediate steps, then report the final answer as structured JSON."""

    adapter = TypeAdapter(MathAnswer)
    output_format = {"type": "json_schema", "schema": adapter.json_schema()}

    backend = ClaudeBackend()
    config = BackendConfig(
        allowed_tools=["Bash"],
        permission_mode="auto",
        max_turns=5,
        system_prompt=system_prompt,
        output_format=output_format,
    )

    await backend.connect(config)
    await backend.send_query(
        "Compute: (7 * 13) + (45 / 9) - 2. "
        "Use the calculator (echo $((...))) for each step. Report the final answer."
    )

    messages: list[BackendMessage] = []
    async for msg in backend.receive_messages():
        messages.append(msg)
        display = (msg.content or msg.raw_result or str(msg.structured_output) or "")[:80]
        print(f"  [{msg.type}] {display}")

    await backend.disconnect()

    result_msgs = [m for m in messages if m.type == "result"]
    assert len(result_msgs) == 1

    result = result_msgs[0]
    if result.structured_output:
        answer = adapter.validate_python(result.structured_output)
    else:
        answer = adapter.validate_json(result.raw_result)

    print(f"  Parsed answer: {answer}")

    # (7 * 13) + (45 / 9) - 2 = 91 + 5 - 2 = 94
    assert answer.result == 94, f"Expected 94, got {answer.result}"
    assert len(answer.steps) >= 1, "Expected at least 1 step"

    tool_msgs = [m for m in messages if m.type == "tool_use"]
    assert len(tool_msgs) >= 1, "Expected at least one calculator invocation"

    print(f"  Cost: ${result.cost_usd:.4f}" if result.cost_usd else "  Cost: N/A")
    print("  PASSED\n")


async def main():
    print("\n" + "=" * 60)
    print("ClaudeBackend Integration Tests")
    print("=" * 60 + "\n")

    await test_single_query_with_tool_use()
    await test_multi_turn_chaining()
    await test_interrupt()
    await test_structured_output_treasure_hunt()
    await test_structured_output_math_puzzle()

    print("=" * 60)
    print("All integration tests passed!")
    print("=" * 60)


if __name__ == "__main__":
    asyncio.run(main())
