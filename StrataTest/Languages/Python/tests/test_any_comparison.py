from typing import Any

def test_any_comparison():
    x: Any = 10
    y: Any = 20
    assert x < y, "comparison on Any"
    assert x != y, "inequality on Any"

test_any_comparison()
