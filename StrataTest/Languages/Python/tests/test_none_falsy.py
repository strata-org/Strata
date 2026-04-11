def test_none_falsy():
    x = None
    r: int = 0
    if x:
        r = 1
    assert r == 0, "None is falsy"

test_none_falsy()
