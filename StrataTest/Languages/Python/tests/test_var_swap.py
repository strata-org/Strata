def test_var_swap():
    a: int = 1
    b: int = 2
    t: int = a
    a = b
    b = t
    assert a == 2 and b == 1, "swap"

test_var_swap()
