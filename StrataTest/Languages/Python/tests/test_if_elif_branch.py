def test_if_elif():
    x: int = 5
    r: int = 0
    if x > 10:
        r = 1
    elif x > 3:
        r = 2
    else:
        r = 3
    assert r == 2, "elif branch"

test_if_elif()
