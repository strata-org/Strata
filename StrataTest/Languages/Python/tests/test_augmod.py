def test_augmod():
    x: int = 17
    x %= 5
    assert x == 2, "augmented mod"

test_augmod()
