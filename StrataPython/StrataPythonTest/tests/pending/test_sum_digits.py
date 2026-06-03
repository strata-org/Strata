def sum_digits(n: int) -> int:
    s: int = 0
    while n > 0:
        s = s + n % 10
        n = n // 10
    return s

def test_sum_digits():
    assert sum_digits(123) == 6, "1+2+3"
    assert sum_digits(999) == 27, "9+9+9"

test_sum_digits()
