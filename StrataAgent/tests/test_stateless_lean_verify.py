"""Test: Stateless LeanVerify agent with dict input and typed output."""

import os
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import asyncio
from dataclasses import dataclass
from pathlib import Path

from strataswarm._agent import SwarmAgent
from strataswarm._channels import ChannelBus
from strataswarm._tokens import CancellationToken, PauseToken
from strataswarm._tools import ToolSet
from strataswarm._types import AgentSpec


@dataclass
class LeanVerifyResult:
    compiles: bool
    has_sorry: bool
    statements_match: bool
    errors: list[str]


def make_lean_verify_spec() -> AgentSpec:
    tools = ToolSet()
    tools.allow("Bash(lake lean*)")
    tools.allow("Read")
    return AgentSpec(
        name="lean_verify_test",
        stateless=True,
        system_prompt="You verify Lean files. Compile, check sorry, compare statements. Return JSON.",
        prompt="",
        tools=tools,
        mcp_servers={"lean_lsp": {"command": "uvx", "args": ["lean-lsp-mcp"], "type": "stdio"}},
    )


async def test_lean_verify():
    from strataswarm._claude_backend import ClaudeBackend

    agent = SwarmAgent(
        spec=make_lean_verify_spec(),
        backend=ClaudeBackend(),
        channel_bus=ChannelBus(),
        cancellation=CancellationToken(),
        pause=PauseToken(),
        cwd=str(Path(__file__).parent.parent.parent),
    )

    inp = {
        "stub_file": "StrataTest/Transform/StrataAgentTestStub.lean",
        "sandbox_file": "StrataTest/Transform/StrataAgentTestSandboxed.lean",
    }

    result = await agent.run(inp=inp, result_type=LeanVerifyResult)

    print(f"Status: {result.status}")
    if result.structured_output:
        out: LeanVerifyResult = result.structured_output
        print(f"Compiles: {out.compiles}, Sorry: {out.has_sorry}, Match: {out.statements_match}")
        if out.errors:
            print(f"Errors: {out.errors}")
    else:
        print(f"Raw: {result.raw_result[:300] if result.raw_result else 'None'}")


async def test_lean_verify_bool():
    """Test with bare bool as result_type — see if SDK handles it."""
    from strataswarm._claude_backend import ClaudeBackend

    agent = SwarmAgent(
        spec=make_lean_verify_spec(),
        backend=ClaudeBackend(),
        channel_bus=ChannelBus(),
        cancellation=CancellationToken(),
        pause=PauseToken(),
        cwd=str(Path(__file__).parent.parent.parent),
    )

    inp = {
        "stub_file": "StrataTest/Transform/StrataAgentTestStub.lean",
        "sandbox_file": "StrataTest/Transform/StrataAgentTestSandboxed.lean",
    }

    try:
        result = await agent.run(inp=inp, result_type=bool)
        print(f"Status: {result.status}")
        print(f"Output(bool): {result.output}, type: {type(result.output)}")
        print(f"Structured output: {result.structured_output} (type: {type(result.structured_output)})")
        print(f"Raw: {result.raw_result[:200] if result.raw_result else 'None'}")
    except Exception as e:
        print(f"FAILED with: {type(e).__name__}: {e}")


if __name__ == "__main__":
    import sys
    asyncio.run(test_lean_verify_bool())
    # if "--bool" in sys.argv:
    #     asyncio.run(test_lean_verify_bool())
    # else:
    #     asyncio.run(test_lean_verify())
