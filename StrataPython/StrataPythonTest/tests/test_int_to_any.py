from typing import Any

def test_int_to_any():
    x: int = 42
    y: Any = x
    assert y == 42, "int assigned to Any"

test_int_to_any()
