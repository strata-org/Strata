def test():
    x: int = 16
    y: int = x >> 2
    assert y == 4, "right shift"
test()
