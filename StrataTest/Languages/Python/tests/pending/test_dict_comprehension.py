def test():
    d = {k: k * 2 for k in [1, 2, 3]}
    assert d[1] == 2, "dict comprehension"
test()
