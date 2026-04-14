from typing import Any

def test_any_bool():
    x: Any = True
    assert x == True, "Any holds bool"

test_any_bool()
