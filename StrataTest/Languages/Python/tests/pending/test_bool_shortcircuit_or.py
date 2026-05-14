def test_bool_shortcircuit_or():
    x: int = 0
    r: bool = (x == 0) or (10 // x > 0)
    assert r, "short circuit or"

test_bool_shortcircuit_or()
