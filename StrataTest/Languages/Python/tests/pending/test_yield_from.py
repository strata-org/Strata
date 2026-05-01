def inner():
    yield 1

def outer():
    yield from inner()

def test():
    g = outer()
    assert next(g) == 1, "yield from"
test()
