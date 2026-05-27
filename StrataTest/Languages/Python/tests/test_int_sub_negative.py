def test_int_sub_negative():
    a: int = 3
    b: int = 10
    c: int = a - b
    assert c == -7, "subtraction yielding negative"

test_int_sub_negative()
