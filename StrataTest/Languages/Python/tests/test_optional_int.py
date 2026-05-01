from typing import Optional

def test_optional_int():
    x: Optional[int] = 5
    assert x == 5, "optional with value"
    x = None
    assert x is None, "optional set to None"

test_optional_int()
