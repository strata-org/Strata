from typing import Optional

def test_type_optional_none():
    x: Optional[int] = None
    assert x is None, "optional none"

test_type_optional_none()
