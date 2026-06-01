"""Tests for DeepProofValidator stateless agent.

Test cases:
- test_complete.lean vs test_stub.lean → True (correct proof)
- test_complete_not_compile.lean vs test_stub.lean → False (doesn't compile)
- test_complete_incorrect.lean vs test_stub.lean → False (different statement)
- test_complete_sorry.lean vs test_stub.lean → False (has sorry)
"""

import os
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import asyncio
from pathlib import Path

import yaml

from strataswarm._agent import SwarmAgent
from strataswarm._channels import ChannelBus
from strataswarm._tokens import CancellationToken, PauseToken
from strataswarm._tools import ToolSet
from strataswarm._types import AgentSpec

PROJECT_ROOT = str(Path(__file__).parent.parent.parent)
LEAN_DIR = Path(__file__).parent / "Lean"


# ─── Test fixtures (created on the fly) ─────────────────────────────────────

LEAN_FILES = {
    "test_stub.lean": """
theorem test_theorem : n + 1 = 1 + n := by sorry
""",
    "test_complete.lean": """
theorem test_theorem : n + 1 = 1 + n := by
  omega
""",
    "test_complete_not_compile.lean": """
theorem test_theorem : n + 1 = 1 + n := by
  simp
""",
    "test_complete_incorrect.lean": """
theorem test_theorem_wrong : n = n := by
  rfl
""",
    "test_complete_sorry.lean": """
theorem test_theorem : n + 1 = 1 + n := by
  simp
  sorry
""",
}


def setup_lean_files():
    """Create test Lean files on the fly."""
    LEAN_DIR.mkdir(parents=True, exist_ok=True)
    for name, content in LEAN_FILES.items():
        (LEAN_DIR / name).write_text(content.strip() + "\n")


def teardown_lean_files():
    """Remove generated Lean files (keep .gitkeep)."""
    for name in LEAN_FILES:
        f = LEAN_DIR / name
        if f.exists():
            f.unlink()


# ─── Agent loading ───────────────────────────────────────────────────────────

def load_deep_proof_validator_spec() -> AgentSpec:
    """Load the DeepProofValidator agent spec from YAML."""
    spec_path = Path(__file__).parent.parent / "strataswarm" / "agent_specs" / "agents" / "deep_proof_validator.yaml"
    with open(spec_path) as f:
        raw = yaml.safe_load(f)

    tools = ToolSet()
    for t in raw.get("allowed_tools", []):
        tools.allow(t)
    for t in raw.get("disallowed_tools", []):
        tools.disallow(t)

    return AgentSpec(
        name=raw["name"],
        stateless=raw.get("stateless", True),
        system_prompt=raw.get("system_prompt", ""),
        prompt=raw.get("prompt", ""),
        tools=tools,
        mcp_servers=raw.get("mcp_servers", {}),
    )


# ─── Runner ──────────────────────────────────────────────────────────────────

async def run_validation(stub: str, complete: str) -> bool | None:
    """Run the DeepProofValidator and return the boolean result."""
    from strataswarm._claude_backend import ClaudeBackend

    spec = load_deep_proof_validator_spec()
    agent = SwarmAgent(
        spec=spec,
        backend=ClaudeBackend(),
        channel_bus=ChannelBus(),
        cancellation=CancellationToken(),
        pause=PauseToken(),
        cwd=PROJECT_ROOT,
    )

    inp = {"stub_file": stub, "complete_file": complete}
    result = await agent.run(inp=inp, result_type=bool)
    return result.output


# ─── Tests ───────────────────────────────────────────────────────────────────

async def test_correct_proof():
    """Correct proof that compiles, no sorry, statements match → True."""
    result = await run_validation(
        stub=str(LEAN_DIR / "test_stub.lean"),
        complete=str(LEAN_DIR / "test_complete.lean"),
    )
    print(f"[correct_proof] Expected: True, Got: {result}")
    assert result is True, f"Expected True, got {result}"


async def test_not_compile():
    """Proof that doesn't compile → False."""
    result = await run_validation(
        stub=str(LEAN_DIR / "test_stub.lean"),
        complete=str(LEAN_DIR / "test_complete_not_compile.lean"),
    )
    print(f"[not_compile] Expected: False, Got: {result}")
    assert result is False, f"Expected False, got {result}"


async def test_incorrect_statement():
    """Proof compiles but proves different theorem → False."""
    result = await run_validation(
        stub=str(LEAN_DIR / "test_stub.lean"),
        complete=str(LEAN_DIR / "test_complete_incorrect.lean"),
    )
    print(f"[incorrect_statement] Expected: False, Got: {result}")
    assert result is False, f"Expected False, got {result}"


async def test_has_sorry():
    """Proof compiles but still has sorry → False."""
    result = await run_validation(
        stub=str(LEAN_DIR / "test_stub.lean"),
        complete=str(LEAN_DIR / "test_complete_sorry.lean"),
    )
    print(f"[has_sorry] Expected: False, Got: {result}")
    assert result is False, f"Expected False, got {result}"


# ─── Custom return type test ─────────────────────────────────────────────────

from dataclasses import dataclass


@dataclass
class DetailedVerifyResult:
    verified: bool
    failure_reason: str | None


async def run_validation_detailed(stub: str, complete: str) -> DetailedVerifyResult | None:
    """Run with custom return type that includes failure reason."""
    from strataswarm._claude_backend import ClaudeBackend

    spec = load_deep_proof_validator_spec()
    agent = SwarmAgent(
        spec=spec,
        backend=ClaudeBackend(),
        channel_bus=ChannelBus(),
        cancellation=CancellationToken(),
        pause=PauseToken(),
        cwd=PROJECT_ROOT,
    )

    inp = {"stub_file": stub, "complete_file": complete}
    result = await agent.run(inp=inp, result_type=DetailedVerifyResult)
    return result.output


async def test_detailed_correct():
    """Correct proof → verified=True, failure_reason=None."""
    result = await run_validation_detailed(
        stub=str(LEAN_DIR / "test_stub.lean"),
        complete=str(LEAN_DIR / "test_complete.lean"),
    )
    print(f"[detailed_correct] Got: {result}")
    assert result is not None
    assert result.verified is True
    assert result.failure_reason is None


async def test_detailed_sorry():
    """Sorry proof → verified=False, failure_reason explains why."""
    result = await run_validation_detailed(
        stub=str(LEAN_DIR / "test_stub.lean"),
        complete=str(LEAN_DIR / "test_complete_sorry.lean"),
    )
    print(f"[detailed_sorry] Got: {result}")
    assert result is not None
    assert result.verified is False
    assert result.failure_reason is not None and len(result.failure_reason) > 0


# ─── has_sorries return type test ────────────────────────────────────────────

@dataclass
class SorryCheckResult:
    has_sorries: bool
    sorry_count: int
    sorry_locations: list[str]


async def run_sorry_check(complete: str) -> SorryCheckResult | None:
    """Run with a sorry-focused return type."""
    from strataswarm._claude_backend import ClaudeBackend

    spec = load_deep_proof_validator_spec()
    agent = SwarmAgent(
        spec=spec,
        backend=ClaudeBackend(),
        channel_bus=ChannelBus(),
        cancellation=CancellationToken(),
        pause=PauseToken(),
        cwd=PROJECT_ROOT,
    )

    inp = {
        "stub_file": str(LEAN_DIR / "test_stub.lean"),
        "complete_file": complete,
    }
    result = await agent.run(inp=inp, result_type=SorryCheckResult)
    return result.output


async def test_sorry_check_clean():
    """Clean proof → has_sorries=False, sorry_count=0."""
    result = await run_sorry_check(str(LEAN_DIR / "test_complete.lean"))
    print(f"[sorry_check_clean] Got: {result}")
    assert result is not None
    assert result.has_sorries is False
    assert result.sorry_count == 0


async def test_sorry_check_with_sorry():
    """Proof with sorry → has_sorries=True, sorry_count>=1, locations non-empty."""
    result = await run_sorry_check(str(LEAN_DIR / "test_complete_sorry.lean"))
    print(f"[sorry_check_with_sorry] Got: {result}")
    assert result is not None
    assert result.has_sorries is True
    assert result.sorry_count >= 1
    assert len(result.sorry_locations) >= 1


# ─── Main ────────────────────────────────────────────────────────────────────

async def run_all():
    print("=" * 50)
    print("DeepProofValidator Tests")
    print("=" * 50)

    setup_lean_files()

    tests = [
        ("correct_proof", test_correct_proof),
        ("not_compile", test_not_compile),
        ("incorrect_statement", test_incorrect_statement),
        ("has_sorry", test_has_sorry),
        ("detailed_correct", test_detailed_correct),
        ("detailed_sorry", test_detailed_sorry),
        ("sorry_check_clean", test_sorry_check_clean),
        ("sorry_check_with_sorry", test_sorry_check_with_sorry),
    ]

    passed = 0
    failed = 0
    for name, test_fn in tests:
        try:
            await test_fn()
            passed += 1
            print(f"  ✓ {name}")
        except AssertionError as e:
            failed += 1
            print(f"  ✗ {name}: {e}")
        except Exception as e:
            failed += 1
            print(f"  ✗ {name}: {type(e).__name__}: {e}")

    teardown_lean_files()
    print(f"\nResults: {passed} passed, {failed} failed")


if __name__ == "__main__":
    asyncio.run(run_all())
