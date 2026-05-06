# Test: exception-raising call inside nested control flow in try body.
# The except handler must still be entered when the call inside the if
# branch raises an exception.

def might_fail(x: int) -> int:
    return x

def test_nested_except() -> bool:
    result: int = 0
    try:
        if True:
            result = might_fail(42)
    except:
        result = -1
    assert result == 42, "should succeed"
    return True

test_nested_except()
