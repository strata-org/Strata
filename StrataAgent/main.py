import asyncio
import os
from pathlib import Path

from claude_agent_sdk import (
    ClaudeSDKClient,
    ClaudeAgentOptions,
    AssistantMessage,
    ResultMessage,
    TextBlock,
)


def get_claude_cli_path() -> str:
    env_path = os.environ.get("STRATA_AGENT_CLAUDE_PATH")
    if env_path:
        return env_path
    default_path = Path.home() / ".toolbox" / "bin" / "claude"
    if default_path.exists():
        return str(default_path)
    raise FileNotFoundError(
        "Claude CLI not found. Set STRATA_AGENT_CLAUDE_PATH or install to ~/.toolbox/bin/claude"
    )


def print_response(message):
    if isinstance(message, AssistantMessage):
        for block in message.content:
            if isinstance(block, TextBlock):
                print(block.text)
    elif isinstance(message, ResultMessage):
        cost = (
            f"${message.total_cost_usd:.4f}"
            if message.total_cost_usd is not None
            else "N/A"
        )
        print(f"\n[done: {message.subtype}, cost: {cost}]")


async def main():
    options = ClaudeAgentOptions(
        allowed_tools=["Read", "Bash", "Glob", "Grep"],
        max_turns=5,
        cli_path=get_claude_cli_path(),
    )

    async with ClaudeSDKClient(options=options) as client:
        await client.query("What files are in the current directory? Briefly describe them.")
        async for message in client.receive_response():
            print_response(message)


if __name__ == "__main__":
    asyncio.run(main())
