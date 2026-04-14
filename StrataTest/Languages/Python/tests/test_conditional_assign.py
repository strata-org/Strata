def test_conditional_assign():
    x: int = 10
    y: int = x + 1 if x > 5 else x - 1
    assert y == 11, "conditional assign"

test_conditional_assign()
