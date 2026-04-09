def test_pass_stmt():
    x: int = 5
    if x > 10:
        pass
    else:
        x = x + 1
    assert x == 6, "pass is noop"

test_pass_stmt()
