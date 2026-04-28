# Test: assert statement with and without message
def validate(x: int) -> None:
    assert x > 0, "x must be positive"
    assert isinstance(x, int)
    result: int = x * 2
    return result

def check_bounds(lo: int, hi: int) -> None:
    assert lo < hi
    assert lo >= 0, f"lo must be non-negative, got {lo}"
