from typing import Optional

class Config:
    name: str
    timeout: Optional[int]

    def __init__(self, name: str, timeout: Optional[int]):
        self.name = name
        self.timeout = timeout

def test_optional_field():
    c1 = Config("a", 30)
    assert c1.timeout == 30, "optional field set"
    c2 = Config("b", None)
    assert c2.timeout is None, "optional field None"

test_optional_field()
