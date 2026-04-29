def fib(n: int) -> int:
    if n <= 1:
        return n
    a: int = 0
    b: int = 1
    i: int = 2
    while i <= n:
        t: int = a + b
        a = b
        b = t
        i = i + 1
    return b

def test_fibonacci():
    assert fib(0) == 0, "fib 0"
    assert fib(1) == 1, "fib 1"
    assert fib(10) == 55, "fib 10"

test_fibonacci()
