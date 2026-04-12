from typing import Any

class Data:
    x: int

    def __init__(self, x: int):
        self.x = x

def test_any_field_access():
    d: Any = Data(42)
    assert d.x == 42, "field access on Any"

test_any_field_access()
