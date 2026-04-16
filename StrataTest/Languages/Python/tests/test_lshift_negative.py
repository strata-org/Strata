def test():
    x: int = 1
    y: int = x << -1
    assert y == 0, "negative left shift"
test()
