def test_for_else():
    r: int = 0
    for x in [1, 2, 3]:
        pass
    else:
        r = 42
    assert r == 42, "for else"

test_for_else()
