# Tests evaluate-once semantics for chained comparisons.
# `f()` should be called exactly once in `a < f() < b`.
# Currently blocked by "local variables in functions are not YET supported"
# in the Laurel-to-Core translator (see #892 for tracking).
counter: int = 0

def f() -> int:
    global counter
    counter = counter + 1
    return 5

def test_chained_compare_eval_once():
    a: int = 1
    b: int = 10
    assert a < f() < b, "chained with function call"
    assert counter == 1, "f() should be called exactly once"

test_chained_compare_eval_once()
