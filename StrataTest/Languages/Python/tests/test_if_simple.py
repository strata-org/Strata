def test_if_simple():
    x: int = 5
    r: int = 0
    if x > 3:
        r = 1
    assert r == 1, "simple if"

test_if_simple()
