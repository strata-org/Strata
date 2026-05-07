from typing import Any

def test_any_dict():
    x: Any = {"a": 1}
    assert x["a"] == 1, "Any holds dict"

test_any_dict()
