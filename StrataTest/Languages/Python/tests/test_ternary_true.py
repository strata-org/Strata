def test_ternary_true():
    x: int = 5
    r: int = 10 if x > 3 else 20
    assert r == 10, "ternary true branch"

test_ternary_true()
