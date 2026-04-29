def test():
    x: int = 42
    x = "hello"
    assert x == "hello", "reassign int to str"
test()
