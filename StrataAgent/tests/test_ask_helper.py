"""Test: ask() helper — quick stateless LLM calls with typed output."""

import os
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import asyncio
from dataclasses import dataclass

from strataswarm import ask


async def test_ask_bool():
    """Simple bool return."""
    result = await ask(
        inp="Is 2 + 2 equal to 4?",
        result_type=bool,
        system_prompt="Answer the math question. Return true or false.",
    )
    print(f"[ask_bool] output={result.output}, type={type(result.output)}")
    assert result.output is True


async def test_ask_dataclass():
    """Structured return type."""
    @dataclass
    class MathResult:
        answer: int
        explanation: str

    result = await ask(
        inp="What is 7 * 6?",
        result_type=MathResult,
        system_prompt="Compute the math expression. Return the answer and a brief explanation.",
    )
    print(f"[ask_dataclass] output={result.output}")
    assert result.output is not None
    assert result.output.answer == 42
    assert len(result.output.explanation) > 0


async def test_ask_no_result_type():
    """Plain text return (no schema enforcement)."""
    result = await ask(
        inp="Say hello in exactly 3 words.",
        system_prompt="Follow the instruction exactly.",
    )
    print(f"[ask_plain] raw={result.raw_result[:100] if result.raw_result else 'None'}")
    assert result.raw_result is not None


async def run_all():
    print("=" * 50)
    print("ask() Helper Tests")
    print("=" * 50)

    tests = [
        ("ask_bool", test_ask_bool),
        ("ask_dataclass", test_ask_dataclass),
        ("ask_no_result_type", test_ask_no_result_type),
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

    print(f"\nResults: {passed} passed, {failed} failed")


if __name__ == "__main__":
    asyncio.run(run_all())
