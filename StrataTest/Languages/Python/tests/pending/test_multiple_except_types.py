def test():
    r: int = 0
    try:
        x: int = 1 // 0
    except (ValueError, ZeroDivisionError):
        r = 1
    assert r == 1, "tuple except"
test()
