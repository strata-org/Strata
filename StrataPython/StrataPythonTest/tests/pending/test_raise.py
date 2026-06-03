def test():
    r: int = 0
    try:
        raise ValueError("oops")
    except ValueError:
        r = 1
    assert r == 1, "raise caught"
test()
