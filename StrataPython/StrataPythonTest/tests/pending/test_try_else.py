def test():
    r: int = 0
    try:
        x: int = 1
    except Exception:
        r = 1
    else:
        r = 2
    assert r == 2, "try else"
test()
