def test_str_falsy():
    s: str = ""
    r: int = 0
    if s:
        r = 1
    assert r == 0, "empty string is falsy"

test_str_falsy()
