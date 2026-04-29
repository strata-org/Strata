def test():
    x: int = 1
    y: int = x << 3
    assert y == 8, "left shift"
test()
