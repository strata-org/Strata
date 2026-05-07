def factorial(n: int) -> int:
    if n <= 1:
        return 1
    return n * factorial(n - 1)

def test_func_recursive():
    assert factorial(5) == 120, "factorial"

test_func_recursive()
