def test_cmp_neq():
    a: int = 1
    b: int = 2
    assert a != b, "not equal"
    assert not (a != 1), "equal"

test_cmp_neq()
