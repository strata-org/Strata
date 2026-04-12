def test():
    x: int | str = 42
    assert x == 42, "union type 3.10 syntax"
test()
