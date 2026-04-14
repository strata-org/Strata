def test_try_except_basic():
    r: int = 0
    try:
        r = 1
    except Exception:
        r = 2
    assert r == 1, "try no exception"

test_try_except_basic()
