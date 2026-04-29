from typing import Any

def test_any_int():
    x: Any = 42
    assert x == 42, "Any holds int"

test_any_int()
