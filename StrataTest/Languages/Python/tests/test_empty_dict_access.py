def test():
    d = {"a": 1}
    r: int = 0
    if "b" in d:
        r = d["b"]
    else:
        r = -1
    assert r == -1, "missing key guarded"
test()
