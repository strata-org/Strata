def clamp(x: int, lo: int, hi: int) -> int:
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x

def test_clamp():
    assert clamp(5, 0, 10) == 5, "in range"
    assert clamp(-1, 0, 10) == 0, "below"
    assert clamp(15, 0, 10) == 10, "above"

test_clamp()
