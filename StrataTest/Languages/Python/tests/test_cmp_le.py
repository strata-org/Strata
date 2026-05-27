def test_cmp_le():
    assert 3 <= 3, "le equal"
    assert 2 <= 3, "le less"
    assert not (4 <= 3), "not le"

test_cmp_le()
