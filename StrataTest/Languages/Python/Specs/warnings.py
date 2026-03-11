from typing import Any, Dict, List, NotRequired, TypedDict, Unpack

# Unsupported assert pattern: equality comparison
def unsupported_assert(**kw: int) -> None:
    assert kw["x"] == 1, 'x must be 1'

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
