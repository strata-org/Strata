def test_chained_compare():
    x: int = 5
    assert 1 < x < 10, "chained compare"
    assert not (10 < x < 1), "reversed bounds should fail"

test_chained_compare()
