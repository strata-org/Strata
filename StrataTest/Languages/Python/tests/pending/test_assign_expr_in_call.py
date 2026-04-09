def add(a: int, b: int) -> int:
    return a + b

def test_assign_expr_in_call():
    r: int = add(2 + 3, 4 * 2)
    assert r == 13, "expressions as arguments"

test_assign_expr_in_call()
