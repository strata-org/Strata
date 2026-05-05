def test_chained_compare_mixed():
    a: int = 1
    b: int = 2
    c: int = 3
    assert a <= b < c, "mixed operators"
    assert c <= a < b, "reversed mixed should fail"
    assert a > 100, "should fail: a is 1"

test_chained_compare_mixed()
