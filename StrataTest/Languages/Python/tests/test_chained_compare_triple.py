def test_chained_compare_triple():
    x: int = 3
    y: int = 7
    assert 1 < x < y < 10, "triple chain"
    assert 10 < x < y < 1, "reversed triple should fail"

test_chained_compare_triple()
