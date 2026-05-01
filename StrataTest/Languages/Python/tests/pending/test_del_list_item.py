def test():
    xs = [1, 2, 3]
    del xs[1]
    assert xs[0] == 1, "first unchanged"
    assert xs[1] == 3, "second shifted"
test()
