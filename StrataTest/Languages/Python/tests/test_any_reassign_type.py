from typing import Any

def test_any_reassign_type():
    x: Any = 42
    x = "now a string"
    assert x == "now a string", "Any reassigned to different type"

test_any_reassign_type()
