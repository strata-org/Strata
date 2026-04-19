from typing import Any

def test_coerce_any_to_bool_falsy():
    x: Any = 0
    r: int = 0
    if x:
        r = 1
    assert r == 0, "Any zero falsy"

test_coerce_any_to_bool_falsy()
