def test_none_conditional():
    x = None
    r: int = 0
    if x is None:
        r = 1
    else:
        r = 2
    assert r == 1, "none conditional"

test_none_conditional()
