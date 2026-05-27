def test_type_int():
    x: int = 42
    y: int = x
    assert y == 42, "int type annotation"

test_type_int()
