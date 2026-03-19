def test_try_no_exception() -> Any:
    result: Any = 0
    try:
        result = 1
    except Exception:
        result = 2
    assert result == 1, "body should have executed"
    return result

def test_try_with_exception() -> Any:
    result: Any = 0
    try:
        raise Exception("err")
        result = 1
    except Exception:
        result = 2
    assert result == 2, "handler should have executed"
    return result
