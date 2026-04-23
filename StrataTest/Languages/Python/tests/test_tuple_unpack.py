def test_tuple_unpack():
    t = (10, 20)
    a, b = t
    assert a == 10, "unpack first"
    assert b == 20, "unpack second"

test_tuple_unpack()
