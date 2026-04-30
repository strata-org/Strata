def test_str_truthy():
    s: str = "hi"
    r: int = 0
    if s:
        r = 1
    assert r == 1, "nonempty string is truthy"

test_str_truthy()
