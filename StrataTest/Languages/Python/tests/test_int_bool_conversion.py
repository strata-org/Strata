def test_int_bool_conversion():
    x: int = 0
    if x:
        r: int = 1
    else:
        r: int = 0
    assert r == 0, "zero is falsy"

test_int_bool_conversion()
