# Fixtures exercising integer arithmetic (`+`, `-`, `*`, `//`, `%`)
# inside predicate bodies.
#
# Each function uses kwargs typed via a TypedDict so the recognizer
# knows the operand types. Successful translation produces zero
# warnings; SpecsTest's predicateArithTestCase asserts exactly that.

from typing import Unpack, TypedDict


Args = TypedDict("Args", {"x": int, "y": int})


def arith_add(**kw: Unpack[Args]) -> None:
    assert kw["x"] + kw["y"] >= 0, "x + y >= 0"


def arith_sub(**kw: Unpack[Args]) -> None:
    assert kw["x"] - kw["y"] <= 100, "x - y <= 100"


def arith_mul_const(**kw: Unpack[Args]) -> None:
    assert kw["x"] * 2 >= kw["y"], "x * 2 >= y"


def arith_floordiv(**kw: Unpack[Args]) -> None:
    assert kw["x"] // 2 < kw["y"], "x // 2 < y"


def arith_mod(**kw: Unpack[Args]) -> None:
    assert kw["x"] % 10 == 0, "x % 10 == 0"
