def test_bool_and():
    a: bool = True
    b: bool = True
    c: bool = False
    assert a and b, "true and true"
    assert not (a and c), "true and false"

test_bool_and()
