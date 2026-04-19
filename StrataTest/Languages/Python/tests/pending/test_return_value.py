def double(x: int) -> int:
    return x * 2

def test_return_value():
    r: int = double(5)
    assert r == 10, "return value"

test_return_value()
