def test():
    xs = [1, 2, 3]
    xs.append(4)
    xs[0] = 10
    assert xs[0] == 10, "modified first"
    assert xs[3] == 4, "appended"
test()
