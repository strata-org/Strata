def test_augmented_assign() -> Any:
    x: Any = 5
    y: Any = x
    y += 3
    assert y == 8, "5 + 3 == 8"
    y -= 2
    assert y == 6, "8 - 2 == 6"
    y *= 2
    assert y == 12, "6 * 2 == 12"
    return y
