def test_bool_not():
    a: bool = True
    b: bool = False
    assert not b, "not false"
    assert not not a, "double negation"

test_bool_not()
