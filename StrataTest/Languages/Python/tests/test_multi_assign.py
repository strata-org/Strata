def test_multi_assign():
    a = b = 5
    assert a == 5, "multi assign a"
    assert b == 5, "multi assign b"

test_multi_assign()
