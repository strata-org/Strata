def test_cmp_eq():
    a: int = 42
    b: int = 42
    assert a == b, "int equality"
    assert not (a == 43), "int inequality"

test_cmp_eq()
