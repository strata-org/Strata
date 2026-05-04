def test_try_except_multi():
    r: int = 0
    try:
        x: int = 1 // 0
    except ValueError:
        r = 1
    except ZeroDivisionError:
        r = 2
    assert r == 2, "correct handler"

test_try_except_multi()
