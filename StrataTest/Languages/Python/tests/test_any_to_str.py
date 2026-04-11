from typing import Any

def test_any_to_str():
    x: Any = "hello"
    y: str = x
    assert y == "hello", "Any assigned to str"

test_any_to_str()
