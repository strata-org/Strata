def test_scope_if_var():
    x: int = 0
    if True:
        x = 10
    assert x == 10, "var set in if visible outside"

test_scope_if_var()
