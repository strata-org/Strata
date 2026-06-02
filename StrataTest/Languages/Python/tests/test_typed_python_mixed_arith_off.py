# strata-args: --check-mode bugFinding --check-level full
# Default-mode counterpart for mixed typed/untyped arithmetic.
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
