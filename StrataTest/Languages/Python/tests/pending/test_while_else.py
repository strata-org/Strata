def test_while_else():
    i: int = 0
    r: int = 0
    while i < 5:
        i = i + 1
    else:
        r = 99
    assert r == 99, "while else"

test_while_else()
