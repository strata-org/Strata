def test_chained_compare_mixed():
    a: int = 1
    b: int = 2
    c: int = 3
    assert a <= b < c, "mixed operators"

test_chained_compare_mixed()
