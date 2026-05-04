def test():
    xs = [1, 2, 3, 4]
    del xs[-1]
    assert xs[0] == 1, "first unchanged"
    assert xs[1] == 2, "second unchanged"
    assert xs[2] == 3, "third unchanged"
test()
