from typing import Any

class Thing:
    val: int

    def __init__(self, val: int):
        self.val = val

def test_coerce_object_to_any():
    t = Thing(5)
    x: Any = t
    assert x.val == 5, "object stored as Any"

test_coerce_object_to_any()
