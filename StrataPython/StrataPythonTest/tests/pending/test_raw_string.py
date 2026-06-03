def test():
    s: str = r"hello\nworld"
    assert "\\" in s, "raw string"
test()
