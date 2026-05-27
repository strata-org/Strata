def test():
    xs = [1, 2, 3, 4, 5]
    r = [y for x in xs if (y := x * 2) > 4]
    assert 6 in r, "walrus operator"
test()
