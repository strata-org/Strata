from typing import Optional

def test_optional_str():
    x: Optional[str] = "hi"
    assert x == "hi", "optional str"
    x = None
    assert x is None, "optional str None"

test_optional_str()
