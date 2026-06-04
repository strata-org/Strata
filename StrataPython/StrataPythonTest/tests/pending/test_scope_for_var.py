def test_scope_for_var():
    last: int = 0
    for x in [1, 2, 3]:
        last = x
    assert last == 3, "var set in for visible outside"

test_scope_for_var()
