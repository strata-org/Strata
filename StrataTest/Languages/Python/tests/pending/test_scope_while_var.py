def test_scope_while_var():
    i: int = 0
    r: int = 0
    while i < 3:
        r = i
        i = i + 1
    assert r == 2, "var set in while visible outside"

test_scope_while_var()
