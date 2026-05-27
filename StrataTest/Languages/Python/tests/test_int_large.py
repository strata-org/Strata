def test_int_large():
    a: int = 1000000
    b: int = 1000000
    c: int = a * b
    assert c == 1000000000000, "large int"

test_int_large()
