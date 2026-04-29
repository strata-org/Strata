def is_even(n: int) -> bool:
    if n == 0:
        return True
    return is_odd(n - 1)

def is_odd(n: int) -> bool:
    if n == 0:
        return False
    return is_even(n - 1)

def test_func_mutual():
    assert is_even(4), "4 is even"
    assert is_odd(3), "3 is odd"

test_func_mutual()
