def test():
    x: int = 16
    y: int = x >> -1
    assert y == 0, "negative right shift"
test()
