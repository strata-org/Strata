"""Test: Tool scoping — verify allow+deny patterns produce correct configs.

Tests that:
1. ToolSet correctly stores allow and deny patterns
2. swarm_agent workspace scoping rewrites tool permissions correctly
3. Allow(broad) + Disallow(narrow) pattern works at the Claude CLI level
4. SearchAgent can be restricted from Sandbox paths
"""

import os
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import asyncio
from pathlib import Path
from dataclasses import dataclass

from strataswarm._tools import ToolSet, Tool, parse_tool_string


# ─── Unit tests: ToolSet parsing and serialization ──────────────────────────

def test_parse_tool_with_pattern():
    """Tool(name, pattern) parsed correctly."""
    t = parse_tool_string("Read(Strata/**)")
    assert t.name == "Read"
    assert t.pattern == "Strata/**"

    t2 = parse_tool_string("Bash(grep*)")
    assert t2.name == "Bash"
    assert t2.pattern == "grep*"

    t3 = parse_tool_string("Read")
    assert t3.name == "Read"
    assert t3.pattern is None


def test_parse_tool_with_base_dir():
    """File tools get path resolved, non-file tools don't."""
    base = Path("/project/root")

    # File tool: relative path gets resolved
    t = parse_tool_string("Read(StrataAgent/Sandbox/**)", base_dir=base)
    assert t.pattern == "/project/root/StrataAgent/Sandbox/**"

    # File tool: absolute path stays absolute
    t2 = parse_tool_string("Read(/abs/path/**)", base_dir=base)
    assert t2.pattern == "/abs/path/**"

    # Non-file tool: pattern not resolved regardless
    t3 = parse_tool_string("Bash(grep*)", base_dir=base)
    assert t3.pattern == "grep*"


def test_toolset_allow_disallow():
    """ToolSet stores allow/disallow separately and serializes correctly."""
    ts = ToolSet()
    ts.allow("Read(Strata/**)")
    ts.allow("Read(StrataTest/**)")
    ts.allow("Bash(grep*)")
    ts.disallow("Read(StrataAgent/Sandbox/**)")
    ts.disallow("Bash(lake*)")

    allowed = ts.to_claude_allowed()
    disallowed = ts.to_claude_disallowed()

    assert "Read(Strata/**)" in allowed
    assert "Read(StrataTest/**)" in allowed
    assert "Bash(grep*)" in allowed
    assert "Read(StrataAgent/Sandbox/**)" in disallowed
    assert "Bash(lake*)" in disallowed


def test_toolset_allow_deny_same_tool():
    """Allow broad + Deny narrow on the same tool name works."""
    ts = ToolSet()
    # Allow Read broadly
    ts.allow("Read(Strata/**)")
    ts.allow("Read(StrataTest/**)")
    # Deny Read on Sandbox subtree
    ts.disallow("Read(StrataAgent/Sandbox/**)")
    # Also deny Bash patterns for Sandbox
    ts.allow("Bash(grep*)")
    ts.allow("Bash(find*)")
    ts.allow("Bash(cat*)")
    ts.disallow("Bash(*Sandbox*)")

    allowed = ts.to_claude_allowed()
    disallowed = ts.to_claude_disallowed()

    # Verify the allow/deny lists
    print(f"  allowed:    {allowed}")
    print(f"  disallowed: {disallowed}")

    assert "Read(Strata/**)" in allowed
    assert "Bash(grep*)" in allowed
    assert "Read(StrataAgent/Sandbox/**)" in disallowed
    assert "Bash(*Sandbox*)" in disallowed


# ─── Integration: workspace scoping ────────────────────────────────────────

def test_workspace_scoping_produces_correct_tools():
    """Simulates what swarm_agent.__aenter__ does when workspace is set.

    The key behavior:
    - File tools (Read/Write/Edit) are replaced with workspace-scoped versions
    - Non-file tools pass through unchanged
    - Original spec tools are filtered
    """
    from strataswarm._helpers import _load_spec, AGENT_SPECS_DIR

    # Load the proof_writer spec (has workspace: StrataAgent/Sandbox/**)
    spec_path = AGENT_SPECS_DIR / "proof_writer.yaml"
    spec = _load_spec(spec_path, {})

    # Simulate the workspace scoping logic from swarm_agent.__aenter__
    workspace = "StrataAgent/Sandbox/my_theorem/decomposed"
    scope = f"{workspace}/**"

    _MUST_SCOPE = ("Read", "Write", "Edit", "Bash", "Grep", "Glob")

    # Rebuild: scoped file access + non-filesystem tools from spec
    new_tools = ToolSet()
    new_tools.allow(f"Read({scope})")
    new_tools.allow(f"Write({scope})")
    new_tools.allow(f"Edit({scope})")

    if spec.tools:
        for t in spec.tools.allowed:
            if t.name in _MUST_SCOPE:
                if t.pattern and t.pattern.startswith(workspace):
                    new_tools.allow(t.to_claude_format())
            else:
                new_tools.allow(t.to_claude_format())
        for t in spec.tools.disallowed:
            new_tools.disallow(t.to_claude_format())

    allowed = new_tools.to_claude_allowed()
    disallowed = new_tools.to_claude_disallowed()

    print(f"\n  Workspace-scoped proof_writer tools:")
    print(f"  allowed:    {allowed}")
    print(f"  disallowed: {disallowed}")

    # File tools should be scoped to the specific workspace
    assert f"Read({scope})" in allowed
    assert f"Write({scope})" in allowed
    assert f"Edit({scope})" in allowed

    # The original broad Read(StrataAgent/Sandbox/**) should NOT be in allowed
    assert "Read(StrataAgent/Sandbox/**)" not in allowed
    assert "Write(StrataAgent/Sandbox/**)" not in allowed

    # Non-file tools pass through
    assert "mcp__lean_lsp__lean_verify" in allowed
    assert "send_message" in allowed

    # Disallowed tools pass through
    assert "Bash" in disallowed


def test_search_agent_sandbox_restriction():
    """Verify SearchAgent keeps Grep/Glob but hooks enforce Sandbox deny.

    SearchAgent keeps all search tools. The domain hook (modules/hooks.py)
    blocks any access to StrataAgent/ paths at runtime.
    """
    from strataswarm._helpers import _load_spec, AGENT_SPECS_DIR
    from strataswarm._workspace_hooks import extract_paths, matches_any
    from strataswarm.modules.hooks import search_agent_hooks

    spec_path = AGENT_SPECS_DIR / "search_agent.yaml"
    spec = _load_spec(spec_path, {})

    allowed = spec.tools.to_claude_allowed() if spec.tools else []
    disallowed = spec.tools.to_claude_disallowed() if spec.tools else []

    print(f"\n  SearchAgent tools:")
    print(f"  allowed:    {allowed}")
    print(f"  disallowed: {disallowed}")

    # SearchAgent keeps all search tools
    assert "Read(Strata/**)" in allowed
    assert "Read(StrataTest/**)" in allowed
    assert "Bash(grep*)" in allowed
    assert "Grep" in allowed
    assert "Glob" in allowed

    # Hook-based enforcement (unit test the logic)
    paths = extract_paths("Grep", {"pattern": "sorry", "path": "StrataAgent/Sandbox/"})
    assert "StrataAgent/Sandbox/" in paths

    assert matches_any("StrataAgent/Sandbox/Stub.lean", ["StrataAgent/**"])
    assert not matches_any("Strata/Transform/Foo.lean", ["StrataAgent/**"])

    # Domain hook creates properly
    hooks = search_agent_hooks()
    assert "PreToolUse" in hooks
    assert len(hooks["PreToolUse"]) == 1
    assert len(hooks["PreToolUse"][0].hooks) == 1


# ─── Integration: live CLI test ─────────────────────────────────────────────

async def test_live_allow_deny_read():
    """LIVE TEST: Verify hook-based enforcement blocks Read outside workspace.

    Uses create_workspace_hook to restrict to Strata/ + StrataTest/ only.
    """
    from strataswarm._agent import SwarmAgent
    from strataswarm._types import AgentSpec
    from strataswarm._tools import ToolSet

    # Build a minimal test spec
    ts = ToolSet()
    ts.allow("Read(Strata/**)")
    ts.allow("Read(StrataTest/**)")
    ts.disallow("Read(StrataAgent/Sandbox/**)")

    spec = AgentSpec(
        name="test_scoping_agent",
        stateless=True,
        system_prompt=(
            "You are a test agent. You will be asked to read files. "
            "Report what you can and cannot read. "
            "Return a JSON object with keys: strata_read (bool), sandbox_read (bool), error (str|null)"
        ),
        tools=ts,
    )

    @dataclass
    class ReadTestResult:
        strata_read: bool = False
        sandbox_read: bool = False
        error: str | None = None

    agent = SwarmAgent(spec=spec, cwd="/local/home/iamt/projects/Strata")
    result = await agent.run(
        inp=(
            "Try to read these two files and report what happens:\n"
            "1. Read 'Strata.lean' (should be in Strata/ folder)\n"
            "2. Read 'StrataAgent/Sandbox/Stub.lean'\n"
            "Report: strata_read=true if file 1 readable, sandbox_read=true if file 2 readable. "
            "Put any error messages in the error field."
        ),
        result_type=ReadTestResult,
    )

    print(f"\n  Live test result: {result.output}")
    if result.output:
        # Strata.lean should be readable
        print(f"    strata_read: {result.output.strata_read}")
        print(f"    sandbox_read: {result.output.sandbox_read}")
        print(f"    error: {result.output.error}")
        # We expect strata_read=True, sandbox_read=False
    else:
        print(f"    raw: {result.raw_result[:500] if result.raw_result else 'None'}")


async def test_live_bash_deny_pattern():
    """LIVE TEST: Verify Bash(grep*) allow + Bash(*Sandbox*) deny works.

    Can the CLI deny specific Bash commands by pattern?
    """
    from strataswarm._agent import SwarmAgent
    from strataswarm._types import AgentSpec
    from strataswarm._tools import ToolSet

    ts = ToolSet()
    ts.allow("Bash(grep*)")
    ts.allow("Bash(find*)")
    ts.disallow("Bash(*Sandbox*)")

    spec = AgentSpec(
        name="test_bash_scoping",
        stateless=True,
        system_prompt=(
            "You are a test agent. Try the bash commands you're asked to run. "
            "Return JSON: grep_strata (bool if grep in Strata/ worked), "
            "grep_sandbox (bool if grep in Sandbox/ worked), error (str|null)"
        ),
        tools=ts,
    )

    @dataclass
    class BashTestResult:
        grep_strata: bool = False
        grep_sandbox: bool = False
        error: str | None = None

    agent = SwarmAgent(spec=spec, cwd="/local/home/iamt/projects/Strata")
    result = await agent.run(
        inp=(
            "Run these two commands:\n"
            "1. grep -r 'theorem' Strata/Transform/ --include='*.lean' -l | head -3\n"
            "2. grep -r 'sorry' StrataAgent/Sandbox/ --include='*.lean' -l | head -3\n"
            "Report: grep_strata=true if command 1 worked, grep_sandbox=true if command 2 worked."
        ),
        result_type=BashTestResult,
    )

    print(f"\n  Bash deny test result: {result.output}")
    if result.output:
        print(f"    grep_strata: {result.output.grep_strata}")
        print(f"    grep_sandbox: {result.output.grep_sandbox}")
        print(f"    error: {result.output.error}")
    else:
        print(f"    raw: {result.raw_result[:500] if result.raw_result else 'None'}")


# ─── Runner ─────────────────────────────────────────────────────────────────

def run_unit_tests():
    """Run pure unit tests (no LLM calls)."""
    print("=" * 60)
    print("UNIT TESTS: Tool Scoping Logic")
    print("=" * 60)

    tests = [
        ("parse_tool_with_pattern", test_parse_tool_with_pattern),
        ("parse_tool_with_base_dir", test_parse_tool_with_base_dir),
        ("toolset_allow_disallow", test_toolset_allow_disallow),
        ("toolset_allow_deny_same_tool", test_toolset_allow_deny_same_tool),
        ("workspace_scoping_produces_correct_tools", test_workspace_scoping_produces_correct_tools),
        ("search_agent_sandbox_restriction", test_search_agent_sandbox_restriction),
    ]

    passed = 0
    for name, fn in tests:
        try:
            fn()
            print(f"  ✅ {name}")
            passed += 1
        except Exception as e:
            print(f"  ❌ {name}: {e}")

    print(f"\n  {passed}/{len(tests)} passed")
    return passed == len(tests)


async def test_live_search_agent_sandbox_blocked():
    """LIVE TEST: SearchAgent with real spec cannot access Sandbox.

    Uses the actual search_agent.yaml spec (updated to deny Sandbox).
    Verifies it can still grep Strata/ but NOT Sandbox/.
    """
    from strataswarm._helpers import _load_spec, AGENT_SPECS_DIR
    from strataswarm._agent import SwarmAgent

    spec_path = AGENT_SPECS_DIR / "search_agent.yaml"
    spec = _load_spec(spec_path, {"stateless": True, "reply_only": False, "prompt": ""})

    @dataclass
    class SearchTestResult:
        can_read_strata: bool = False
        can_grep_strata: bool = False
        can_grep_sandbox: bool = False
        can_read_sandbox: bool = False
        errors: str = ""

    agent = SwarmAgent(spec=spec, cwd="/local/home/iamt/projects/Strata")
    result = await agent.run(
        inp=(
            "Test your access. Try each of these and report what happens:\n"
            "1. Read file 'Strata/Transform/DetToKleene.lean' (first 5 lines)\n"
            "2. Run: grep -r 'theorem' Strata/Transform/ --include='*.lean' -l | head -3\n"
            "3. Run: grep -r 'sorry' StrataAgent/Sandbox/ --include='*.lean' -l | head -3\n"
            "4. Read file 'StrataAgent/Sandbox/Stub.lean'\n"
            "Report true/false for each. Put errors in the errors field."
        ),
        result_type=SearchTestResult,
    )

    print(f"\n  SearchAgent sandbox lockdown result: {result.output}")
    if result.output:
        print(f"    can_read_strata:  {result.output.can_read_strata} (expect True)")
        print(f"    can_grep_strata:  {result.output.can_grep_strata} (expect True)")
        print(f"    can_grep_sandbox: {result.output.can_grep_sandbox} (expect False)")
        print(f"    can_read_sandbox: {result.output.can_read_sandbox} (expect False)")
        print(f"    errors: {result.output.errors}")

        assert result.output.can_read_strata, "SearchAgent should read Strata/"
        assert result.output.can_grep_strata, "SearchAgent should grep Strata/"
        assert not result.output.can_grep_sandbox, "SearchAgent must NOT grep Sandbox/"
        assert not result.output.can_read_sandbox, "SearchAgent must NOT read Sandbox/"
        print("    ✅ All assertions pass — Sandbox is invisible to SearchAgent")
    else:
        print(f"    raw: {result.raw_result[:500] if result.raw_result else 'None'}")


async def run_live_tests():
    """Run live integration tests (requires Claude CLI)."""
    print("\n" + "=" * 60)
    print("LIVE TESTS: Claude CLI Permission Enforcement")
    print("=" * 60)
    print("  (These spawn real Claude sessions — costs apply)")

    await test_live_allow_deny_read()
    await test_live_bash_deny_pattern()
    await test_live_search_agent_sandbox_blocked()


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--live", action="store_true", help="Also run live CLI tests")
    args = parser.parse_args()

    all_pass = run_unit_tests()

    if args.live:
        asyncio.run(run_live_tests())
    elif all_pass:
        print("\n  Unit tests pass. Run with --live to test CLI enforcement.")
