from typing import Any

def test_any_none():
    x: Any = None
    assert x is None, "Any holds None"

test_any_none()
