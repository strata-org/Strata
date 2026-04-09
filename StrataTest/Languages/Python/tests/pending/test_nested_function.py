def outer():
    def inner():
        return 42
    return inner()

def test():
    r = outer()
    assert r == 42, "nested function"
test()
