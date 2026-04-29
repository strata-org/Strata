from typing import Any

class Container:
    data: Any

    def __init__(self, data: Any):
        self.data = data

def test_any_field():
    c = Container(99)
    assert c.data == 99, "Any field"

test_any_field()
