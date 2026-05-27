def test():
    x: int = 0
    y: bool = not x
    assert y == True, "int as bool"
test()
