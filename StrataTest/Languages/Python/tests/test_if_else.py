def test_if_else():
    x: int = 2
    r: int = 0
    if x > 10:
        r = 1
    else:
        r = 2
    assert r == 2, "if else"

test_if_else()
