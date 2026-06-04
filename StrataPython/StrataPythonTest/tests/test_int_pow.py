def test_int_pow():
    a: int = 2
    b: int = 10
    c: int = a ** b
    assert c == 1024, "int power"

test_int_pow()
