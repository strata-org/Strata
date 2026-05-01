def test_bool_or():
    a: bool = True
    b: bool = False
    assert a or b, "true or false"
    assert not (b or b), "false or false"

test_bool_or()
