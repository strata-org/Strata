def test():
    xs = [1, 2, 3, 4, 5]
    del xs[1:3]
    assert xs[0] == 1, "first unchanged"
    assert xs[1] == 4, "fourth shifted"
    assert xs[2] == 5, "fifth shifted"
test()
