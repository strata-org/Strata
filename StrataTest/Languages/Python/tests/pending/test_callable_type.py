from typing import Callable

def apply(f: Callable[[int], int], x: int) -> int:
    return f(x)

def double(x: int) -> int:
    return x * 2

def test():
    r: int = apply(double, 5)
    assert r == 10, "callable type"
test()
