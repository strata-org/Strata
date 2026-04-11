def test():
    g = (x * 2 for x in [1, 2, 3])
    first = next(g)
    assert first == 2, "generator expression"
test()
