def gcd(a: int, b: int) -> int:
    while b != 0:
        t: int = b
        b = a % b
        a = t
    return a

def test_gcd():
    assert gcd(12, 8) == 4, "gcd 12 8"
    assert gcd(7, 13) == 1, "gcd primes"

test_gcd()
