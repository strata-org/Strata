def clamp_positive(x: int) -> int:
    if x <= 0:
        return 0
    if x > 100:
        return 100
    return x

def test_return_early():
    assert clamp_positive(-5) == 0, "early return for negative"
    assert clamp_positive(50) == 50, "no early return"
    assert clamp_positive(200) == 100, "early return for large"

test_return_early()
