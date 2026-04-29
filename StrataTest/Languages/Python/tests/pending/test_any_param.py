from typing import Any

def process(x: Any) -> int:
    return x + 1

def test_any_param():
    r: int = process(10)
    assert r == 11, "Any parameter"

test_any_param()
