def test():
    xs = [x * 2 for x in [1, 2, 3]]
    assert xs[0] == 2, "list comprehension"
test()
