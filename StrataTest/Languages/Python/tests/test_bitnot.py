def test():
    x: int = 0
    y: int = ~x
    assert y == -1, "bitwise not"
test()
