def test():
    a, *b = [1, 2, 3, 4]
    assert a == 1, "first"
    assert b[0] == 2, "rest first"
test()
