from typing import Any, Dict, List, NotRequired, TypedDict, Unpack

# Unsupported assert pattern: chained comparison (more than one operator)
def unsupported_assert(**kw: int) -> None:
    assert 0 <= kw["x"] <= 10, '0 <= x <= 10'

# Unsupported __init__ assignment value (not self._ClassName() pattern)
class BadInit:
    def __init__(self):
        self.name = "hello"

# Skipped Assign in function body
def skipped_assign(**kw: int) -> None:
    x = kw["a"]
    assert x >= 1, 'x >= 1'

# For loop with unsupported target (attribute, not simple Name)
LoopRequest = TypedDict('LoopRequest', {
    'Items': NotRequired[List[str]],
    'Data': NotRequired[Dict[str, str]],
})

# For loop with unsupported orelse (for/else)
def for_else_loop(**kw: Unpack[LoopRequest]) -> None:
    for item in kw["Items"]:
        assert len(item) >= 1, f'Expected len >= 1'
    else:
        pass

# Skipped Expr in function body (non-ellipsis expression statement)
def skipped_expr(**kw: int) -> None:
    kw["a"]

# Floor division with a non-positive-literal divisor: Python `//` and
# Laurel `Div` (Euclidean) only agree when the divisor is a positive
# literal, so the recognizer emits a warning.
DivArgs = TypedDict('DivArgs', {'x': int, 'y': int})

def floor_div_symbolic_divisor(**kw: Unpack[DivArgs]) -> None:
    assert kw["x"] // kw["y"] >= 0, "x // y >= 0"

# Comparison between two `Any`-typed operands. The recognizer can't
# tell whether the operands are int or float and assumes int; if the
# runtime values are floats the generated VC has the wrong sort, so a
# warning is emitted.
AnyArgs = TypedDict('AnyArgs', {'x': Any, 'y': Any})

def compare_any_to_any(**kw: Unpack[AnyArgs]) -> None:
    assert kw["x"] < kw["y"], "x < y"
