from typing import Any

def test_any_in_if():
    x: Any = 5
    r: int = 0
    if x > 3:
        r = 1
    assert r == 1, "Any in condition"

test_any_in_if()
