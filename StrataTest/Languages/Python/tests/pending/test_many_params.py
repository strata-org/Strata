def f(a: int, b: int, c: int, d: int, e: int, f_: int, g: int, h: int) -> int:
    return a + b + c + d + e + f_ + g + h

def test():
    r: int = f(1, 2, 3, 4, 5, 6, 7, 8)
    assert r == 36, "8 params"
test()
