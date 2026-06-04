def test():
    s: str = "abc"
    r: str = ""
    for c in s:
        r = r + c
    assert r == "abc", "iterate string"
test()
