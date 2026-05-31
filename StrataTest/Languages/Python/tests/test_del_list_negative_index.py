def test():
    xs = [1, 2, 3, 4]
    del xs[-1]
    assert xs[0] == 1, "first unchanged"
    assert xs[1] == 2, "second unchanged"
    assert xs[2] == 3, "third unchanged"


def test_index_error():
    xs = [1, 2, 3]
    del xs[-4]
    ys = [2]
    del ys[-1]
