from typing import Any

class Box:
    val: Any

    def __init__(self, val: Any):
        self.val = val

def test_any_field_reassign():
    b = Box(1)
    assert b.val == 1, "initial int"
    b.val = "hello"
    assert b.val == "hello", "reassigned to str"

test_any_field_reassign()
