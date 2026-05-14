from typing import Any

def test_coerce_none_to_any():
    x: Any = None
    r: int = 0
    if x is None:
        r = 1
    assert r == 1, "None in Any"

test_coerce_none_to_any()
