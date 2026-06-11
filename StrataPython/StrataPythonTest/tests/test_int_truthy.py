def test_int_truthy():
    x: int = 42
    r: int = 0
    if x:
        r = 1
    assert r == 1, "nonzero is truthy"

test_int_truthy()
