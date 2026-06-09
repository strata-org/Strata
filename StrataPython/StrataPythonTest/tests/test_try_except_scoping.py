def test_nested_try_except() -> Any:
    """Nested try/except blocks must produce unique block labels."""
    result: Any = 0
    try:
        try:
            result = 1
        except Exception:
            result = 2
        try:
            result = result
        except Exception:
            result = 3
    except Exception:
        result = 4
    assert result == 1, "inner try body should have executed"
    return result

def test_var_declared_in_both_branches() -> Any:
    """Variable assigned in both try and except must be visible after the block."""
    try:
        x: Any = 1
    except Exception:
        x: Any = 2
    assert x == 1, "x should be visible after try/except"
    return x

def test_multiple_assignments_in_try() -> Any:
    """Multiple variable assignments in try must not cause duplicate declarations."""
    try:
        x: Any = 1
        y: Any = 2
    except Exception:
        x: Any = 10
        y: Any = 20
    assert x == 1, "x from try body"
    return x
