def test():
    x: int = 0
    def inner():
        nonlocal x
        x = 10
    inner()
    assert x == 10, "nonlocal"
test()
