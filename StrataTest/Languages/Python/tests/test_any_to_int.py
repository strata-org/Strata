from typing import Any

def test_any_to_int():
    x: Any = 42
    y: int = x
    assert y == 42, "Any assigned to int"

test_any_to_int()
