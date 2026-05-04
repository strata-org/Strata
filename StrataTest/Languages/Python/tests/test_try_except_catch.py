def test_try_except_catch():
    r: int = 0
    try:
        x: int = 1 // 0
        r = 1
    except ZeroDivisionError:
        r = 2
    assert r == 2, "caught exception"

test_try_except_catch()
