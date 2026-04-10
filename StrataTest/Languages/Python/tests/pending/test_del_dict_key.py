def test():
    d = {"a": 1, "b": 2}
    del d["a"]
    assert "a" not in d, "key deleted"
test()
