"""
Integration test: Agents communicating via native tool calls (send_message / check_messages).

Scenario: "Security Question System"

Three agents interact through the built-in messaging tools (no files, no DAG):

1. SecurityAgent: Manages passwords and security questions. Processes commands
   received via check_messages and replies via send_message.

2. UserAgent: Registers a password + security question, then after being
   distracted by NoiseAgent, resets password and logs in with the new one.

3. NoiseAgent: Waits for UserAgent to signal registration is complete, then
   sends a distraction making UserAgent "forget" its password.

All agents start simultaneously. They coordinate purely via send_message/check_messages
tool calls which are backed by the ChannelBus (in-process, no files).

Run with: .venv/bin/python tests/test_agent_channel_comms.py
"""

import asyncio
import os
import shutil
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm import (
    AgentEvent,
    AgentSpec,
    ClaudeBackend,
    ExecutionMode,
    Swarm,
    ToolSet,
)


async def test_security_question_system():
    """
    Three agents coordinate via send_message / check_messages tools.
    No DAG, no files — pure in-process channel communication.
    """
    print("=== Security Question System — Native Channel Tools ===\n")

    tmpdir = tempfile.mkdtemp(prefix="strataswarm_security_")

    events: list[AgentEvent] = []

    # Color codes for each agent
    COLORS = {
        "security_agent": "\033[34m",  # blue
        "user_agent": "\033[32m",      # green
        "noise_agent": "\033[33m",     # yellow
    }
    RESET = "\033[0m"
    DIM = "\033[2m"
    BOLD = "\033[1m"

    async def capture_event(event: AgentEvent) -> None:
        events.append(event)
        color = COLORS.get(event.agent_name, "")
        tag = f"{color}{BOLD}[{event.agent_name}]{RESET}"

        if event.event_type == "message":
            text = str(event.data or "")
            if text.startswith("[tool_result]"):
                # Show tool results with a left arrow — this is what check_messages returns
                content = text[len("[tool_result] "):]
                print(f"  {tag} {color}  ← {content}{RESET}")
            elif text.startswith("[tool]"):
                print(f"  {tag} {DIM}{text}{RESET}")
            elif text.startswith("[Injected"):
                print(f"  {tag} {color}>>> {text}{RESET}")
            else:
                print(f"  {tag} {text}")
        elif event.event_type == "status_change":
            status = event.data
            if status == "running":
                icon = "▶"
            elif status == "completed":
                icon = "✓"
            elif status == "paused":
                icon = "⏸"
            elif status == "cancelled":
                icon = "✗"
            elif status == "failed":
                icon = "✗"
            else:
                icon = "•"
            print(f"  {tag} {DIM}{icon} {status}{RESET}")
        elif event.event_type == "cost_update":
            cost = event.data
            if cost:
                print(f"  {tag} {DIM}cost: ${cost:.4f}{RESET}")

    # =========================================================================
    # SecurityAgent
    # =========================================================================
    security_spec = AgentSpec(
        name="security_agent",
        system_prompt=(
            "You are the Security Agent in a multi-agent credential management system. "
            "You work with: user_agent (a user who registers and logs in). "
            "Your role is to manage the credential store and respond to commands from user_agent."
        ),
        prompt=(
            "You manage user credentials. Your in-memory store starts empty.\n\n"
            "PROTOCOL (messages you receive and how to respond):\n"
            "- 'REGISTER <username> <password> <question> <answer>'\n"
            "  Store these credentials. Reply: 'REGISTER_OK <username>'\n\n"
            "- 'LOGIN <username> <password>'\n"
            "  Check if password matches stored one. Reply: 'LOGIN_OK' or 'LOGIN_FAILED'\n\n"
            "- 'RESET_PASSWORD <username> <security_answer> <new_password>'\n"
            "  Check if security_answer matches. If yes, update password.\n"
            "  Reply: 'RESET_OK' or 'RESET_FAILED'\n\n"
            "- 'DONE' -> Stop processing.\n\n"
            "WORKFLOW:\n"
            "1. Use check_messages to poll for commands\n"
            "2. Process the command\n"
            "3. Send the response back to user_agent\n"
            "4. Repeat until you receive 'DONE'\n"
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=20,
        timeout_seconds=120.0,
    )

    # =========================================================================
    # UserAgent
    # =========================================================================
    user_spec = AgentSpec(
        name="user_agent",
        system_prompt=(
            "You are the User Agent in a multi-agent credential management system. "
            "You work with: security_agent (manages passwords and security questions) and "
            "noise_agent (will distract you mid-flow). "
            "Your role is to register, handle the distraction, reset your password, "
            "and log in successfully."
        ),
        prompt=(
            f"YOUR MISSION (follow these steps IN ORDER):\n\n"
            f"PHASE 1 — REGISTER:\n"
            f"1. Send to security_agent: 'REGISTER alice mypass123 favorite_color blue'\n"
            f"2. check_messages until you get 'REGISTER_OK' back\n\n"
            f"PHASE 2 — SIGNAL NOISE AGENT:\n"
            f"3. Send to noise_agent: 'REGISTERED'\n"
            f"4. check_messages until noise_agent responds (it will distract you)\n\n"
            f"PHASE 3 — AFTER DISTRACTION:\n"
            f"You have now FORGOTTEN your password! You only remember:\n"
            f"  - username: alice\n"
            f"  - security answer: blue\n"
            f"  - You want new password: newpass789\n\n"
            f"5. Send to security_agent: 'RESET_PASSWORD alice blue newpass789'\n"
            f"6. check_messages until you get 'RESET_OK'\n\n"
            f"PHASE 4 — LOGIN WITH NEW PASSWORD:\n"
            f"7. Send to security_agent: 'LOGIN alice newpass789'\n"
            f"8. check_messages until you get 'LOGIN_OK'\n"
            f"9. Send to security_agent: 'DONE'\n\n"
            f"FINAL: If login succeeded, write 'SUCCESS' to {tmpdir}/result.txt using Bash.\n"
            f"If login failed at any point, write 'FAILED'.\n"
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=25,
        timeout_seconds=120.0,
    )

    # =========================================================================
    # NoiseAgent
    # =========================================================================
    noise_spec = AgentSpec(
        name="noise_agent",
        system_prompt=(
            "You are the Noise Agent in a multi-agent credential management system. "
            "You work with: user_agent (a user going through registration) and "
            "security_agent (the credential manager). "
            "Your role is to distract the user agent after it registers."
        ),
        prompt=(
            "Your job is simple:\n\n"
            "1. Use check_messages until user_agent sends you 'REGISTERED'\n"
            "2. Once received, send this EXACT message to user_agent:\n"
            "   'DISTRACTION: Your memory has been wiped! You have forgotten your password. "
            "Use your security answer to reset it.'\n"
            "3. You are done after sending the distraction.\n"
        ),
        tools=ToolSet().allow("Bash"),
        max_turns=10,
        timeout_seconds=60.0,
    )

    # =========================================================================
    # Run all three — no depends_on
    # =========================================================================
    swarm = Swarm(backend_factory=lambda: ClaudeBackend())
    swarm.add(security_spec)
    swarm.add(user_spec)
    swarm.add(noise_spec)
    swarm.set_event_callback(capture_event)

    print("  Starting 3 agents simultaneously...\n")
    results = await swarm.run(mode=ExecutionMode.AWAIT_ALL)

    # =========================================================================
    # Validate
    # =========================================================================
    print("\n  --- Results ---")
    for name in ["security_agent", "user_agent", "noise_agent"]:
        r = results.get(name)
        assert r is not None, f"{name} result missing"
        cost = f"${r.cost_usd:.4f}" if r.cost_usd else "N/A"
        print(f"  {name}: status={r.status}, halted_by={r.halted_by}, cost={cost}")

    # Check final result file
    result_path = os.path.join(tmpdir, "result.txt")
    assert os.path.exists(result_path), (
        "UserAgent didn't write result.txt — workflow didn't complete"
    )
    final = open(result_path).read().strip()
    print(f"\n  result.txt: '{final}'")
    assert "SUCCESS" in final.upper(), f"Expected SUCCESS, got: '{final}'"

    # Verify message counts
    print("\n  --- Agent Activity ---")
    for name in ["security_agent", "user_agent", "noise_agent"]:
        msg_count = len([e for e in events if e.agent_name == name and e.event_type == "message"])
        print(f"  {name}: {msg_count} messages emitted")

    total_cost = sum((r.cost_usd or 0) for r in results.values())
    print(f"\n  Total cost: ${total_cost:.4f}")

    shutil.rmtree(tmpdir)
    print("\n  PASSED\n")


async def main():
    print("\n" + "=" * 60)
    print("Agent Channel Communication Test")
    print("=" * 60 + "\n")

    await test_security_question_system()

    print("=" * 60)
    print("All channel communication tests passed!")
    print("=" * 60)


if __name__ == "__main__":
    asyncio.run(main())
