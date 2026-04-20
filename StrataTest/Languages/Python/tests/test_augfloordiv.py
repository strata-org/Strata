def test_augfloordiv():
    x: int = 20
    x //= 3
    assert x == 6, "augmented floordiv"

test_augfloordiv()
