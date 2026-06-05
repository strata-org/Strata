def test_ternary_nested():
    x: int = 5
    r: str = "big" if x > 10 else ("mid" if x > 3 else "small")
    assert r == "mid", "nested ternary"

test_ternary_nested()
