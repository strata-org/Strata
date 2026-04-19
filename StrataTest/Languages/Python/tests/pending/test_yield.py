def gen():
    yield 1
    yield 2

def test():
    g = gen()
    assert next(g) == 1, "yield"
test()
