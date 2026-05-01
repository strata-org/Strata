def add6(a: int, b: int, c: int, d: int, e: int, f_: int) -> int:
    return a + b + c + d + e + f_

def test():
    r: int = add6(1, 2, 3, 4, 5, 6)
    assert r == 21, "sum of 6"
test()
