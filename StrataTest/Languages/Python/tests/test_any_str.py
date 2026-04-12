from typing import Any

def test_any_str():
    x: Any = "hello"
    assert x == "hello", "Any holds str"

test_any_str()
