from typing import Any

def test_coerce_any_str_concat():
    x: Any = "hello"
    y: str = " world"
    z = x + y
    assert z == "hello world", "Any str concat"

test_coerce_any_str_concat()
