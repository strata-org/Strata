def power(base: int, exp: int) -> int:
    result: int = 1
    i: int = 0
    while i < exp:
        result = result * base
        i = i + 1
    return result

def test_power_iterative():
    assert power(2, 10) == 1024, "2^10"
    assert power(3, 0) == 1, "x^0"

test_power_iterative()
