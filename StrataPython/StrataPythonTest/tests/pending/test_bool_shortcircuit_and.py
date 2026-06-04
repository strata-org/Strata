def test_bool_shortcircuit_and():
    x: int = 0
    r: bool = (x != 0) and (10 // x > 0)
    assert not r, "short circuit and"

test_bool_shortcircuit_and()
