def test():
    x: int = 0b1100
    y: int = 0b1010
    z: int = x ^ y
    assert z == 0b0110, "bitwise xor"
test()
