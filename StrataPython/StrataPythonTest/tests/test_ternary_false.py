def test_ternary_false():
    x: int = 1
    r: int = 10 if x > 3 else 20
    assert r == 20, "ternary false branch"

test_ternary_false()
