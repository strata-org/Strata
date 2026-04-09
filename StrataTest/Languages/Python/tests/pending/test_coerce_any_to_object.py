from typing import Any

class Thing:
    val: int

    def __init__(self, val: int):
        self.val = val

def test_coerce_any_to_object():
    x: Any = Thing(7)
    t: Thing = x
    assert t.val == 7, "Any back to object"

test_coerce_any_to_object()
