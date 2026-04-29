from typing import Any

def get_value() -> Any:
    return 42

def test_any_return():
    r: Any = get_value()
    assert r == 42, "Any return"

test_any_return()
