def test_cmp_ge():
    assert 3 >= 3, "ge equal"
    assert 4 >= 3, "ge greater"
    assert not (2 >= 3), "not ge"

test_cmp_ge()
