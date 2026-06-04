def is_prime(n: int) -> bool:
    if n < 2:
        return False
    i: int = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i = i + 1
    return True

def test_is_prime():
    assert not is_prime(1), "1 not prime"
    assert is_prime(2), "2 prime"
    assert is_prime(7), "7 prime"
    assert not is_prime(9), "9 not prime"

test_is_prime()
