from typing import Any

def test_coerce_any_to_bool_truthy():
    x: Any = 1
    r: int = 0
    if x:
        r = 1
    assert r == 1, "Any int truthy"

test_coerce_any_to_bool_truthy()
