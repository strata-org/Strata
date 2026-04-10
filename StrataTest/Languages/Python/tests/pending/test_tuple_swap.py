def test_tuple_swap():
    a: int = 1
    b: int = 2
    a, b = b, a
    assert a == 2 and b == 1, "tuple swap"

test_tuple_swap()
