def test():
    s: str = "a" * 1000
    assert s[999] == "a", "long string"
test()
