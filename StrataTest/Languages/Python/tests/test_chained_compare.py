def test_chained_compare():
    x: int = 5
    assert 1 < x < 10, "chained compare"
    assert 10 < x < 1, "reversed bounds should fail"
    assert x > 100, "should fail: x is 5"

test_chained_compare()
