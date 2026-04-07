def test_int_bool_conversion():
    x: int = 0
    r: int = 0
    if x:
        r = 1
    assert r == 0, "zero is falsy"

test_int_bool_conversion()
