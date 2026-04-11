def test():
    x: int = 0b1100
    y: int = 0b1010
    z: int = x | y
    assert z == 0b1110, "bitwise or"
test()
