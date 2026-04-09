def test_for_else_break():
    r: int = 0
    for x in [1, 2, 3]:
        if x == 2:
            break
    else:
        r = 42
    assert r == 0, "for else skipped on break"

test_for_else_break()
