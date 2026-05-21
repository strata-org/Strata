# Fixtures exercising strict comparisons (`<` `>`) and equality
# (`==` `!=`) between integer-typed predicate operands.
#
# Each function uses kwargs typed via a TypedDict so the recognizer
# knows the operand types. Successful translation produces zero
# warnings; SpecsTest's predicateCompareTestCase asserts exactly that.

from typing import Unpack, TypedDict


Args = TypedDict("Args", {"x": int, "y": int})


def strict_lt(**kw: Unpack[Args]) -> None:
    assert kw["x"] < 10, "x < 10"


def strict_gt(**kw: Unpack[Args]) -> None:
    assert kw["x"] > 0, "x > 0"


def equality_with_literal(**kw: Unpack[Args]) -> None:
    assert kw["x"] == 0, "x == 0"


def inequality_var_to_var(**kw: Unpack[Args]) -> None:
    assert kw["x"] != kw["y"], "x != y"


def equality_var_to_var(**kw: Unpack[Args]) -> None:
    assert kw["x"] == kw["y"], "x == y"


def strict_lt_var_to_var(**kw: Unpack[Args]) -> None:
    assert kw["x"] < kw["y"], "x < y"
