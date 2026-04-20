def test_chained_compare_mixed():
    a: int = 1
    b: int = 2
    c: int = 3
    assert a <= b < c, "mixed operators"
    assert not (c <= a < b), "reversed mixed should fail"

test_chained_compare_mixed()
