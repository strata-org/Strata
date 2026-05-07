from typing import Any

def test_coerce_any_in_comparison():
    x: Any = 10
    y: int = 10
    assert x == y, "Any compared to int"

test_coerce_any_in_comparison()
