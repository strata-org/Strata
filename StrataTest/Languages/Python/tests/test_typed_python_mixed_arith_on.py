# strata-args: --typed-python --check-mode bugFinding --check-level full
# Mixed arithmetic: typed and untyped operands. The native operator
# dispatch must NOT fire when only one operand is typed; the Any
# path takes over and the typed operand is widened at the boundary.
def typed_and_any_add(a: int, b) -> int:
    assert a >= 0
    return a + b


def typed_and_any_mul(a: int, b) -> int:
    assert a >= 0
    return a * b


def any_first_then_typed(a, b: int) -> int:
    assert b >= 0
    return a + b


def typed_int_and_typed_str(a: int, s: str) -> str:
    return s + s
