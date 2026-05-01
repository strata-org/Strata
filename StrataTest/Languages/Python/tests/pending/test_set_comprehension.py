def test():
    s = {x * 2 for x in [1, 2, 3]}
    assert 2 in s, "set comprehension"
test()
