def add3(a: int, b: int, c: int) -> int:
    return a + b + c

def test_multi_param():
    r: int = add3(1, 2, 3)
    assert r == 6, "multi param"

test_multi_param()
