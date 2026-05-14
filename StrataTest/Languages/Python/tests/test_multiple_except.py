def test_except_with_as() -> Any:
    result: Any = 0
    try:
        raise Exception("test error")
        result = 1
    except Exception as e:
        result = 2
    assert result == 2, "except as should have caught exception"
    return result

def test_bare_raise() -> Any:
    result: Any = 0
    try:
        try:
            raise Exception("inner")
        except Exception:
            result = 1
            raise
    except Exception:
        result = 2
    assert result == 2, "bare raise should have re-raised"
    return result

def test_try_except_else_like() -> Any:
    result: Any = 0
    try:
        x: Any = 1
    except Exception:
        result = 2
    result = x
    assert result == 1, "x should be set from try body"
    return result
