from typing import Optional

def test_type_optional_value():
    x: Optional[int] = 5
    assert x == 5, "optional with value"

test_type_optional_value()
