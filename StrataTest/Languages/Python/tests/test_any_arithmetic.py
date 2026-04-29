from typing import Any

def test_any_arithmetic():
    x: Any = 10
    y: Any = 20
    z: Any = x + y
    assert z == 30, "arithmetic on Any"

test_any_arithmetic()
