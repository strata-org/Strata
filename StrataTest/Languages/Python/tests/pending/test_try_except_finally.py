def test_try_except_finally():
    r: int = 0
    f: int = 0
    try:
        r = 1
    except Exception:
        r = 2
    finally:
        f = 99
    assert r == 1, "try body"
    assert f == 99, "finally ran"

test_try_except_finally()
