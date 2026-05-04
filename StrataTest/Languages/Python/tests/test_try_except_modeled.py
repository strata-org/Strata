# Test: modeled procedure calls in try body that set maybe_except.
# Dict access (Any_get) and arithmetic (PAdd) are modeled operations
# that can raise exceptions. The isError check must be inserted after
# these calls so the except handler is entered on failure.

def test_try_dict_access() -> bool:
    d: dict = {"key": "value"}
    result: str = ""
    try:
        result = d["key"]
    except:
        result = "error"
    assert result == "value", "dict access should succeed"
    return True

def test_try_arithmetic() -> bool:
    x: int = 10
    y: int = 3
    result: int = 0
    try:
        result = x + y
    except:
        result = -1
    assert result == 13, "addition should succeed"
    return True

# Modeled call inside nested control flow in try body.
# The isError check must still be inserted even though the
# dict access is inside an if branch.
def test_try_nested_dict_access() -> bool:
    d: dict = {"key": "value"}
    result: str = ""
    try:
        if True:
            result = d["key"]
    except:
        result = "error"
    assert result == "value", "nested dict access should succeed"
    return True

test_try_dict_access()
test_try_arithmetic()
test_try_nested_dict_access()
