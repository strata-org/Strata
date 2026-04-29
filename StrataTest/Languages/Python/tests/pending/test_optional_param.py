from typing import Optional

def greet(name: Optional[str]) -> str:
    if name is None:
        return "hello stranger"
    return "hello " + name

def test_optional_param():
    r1: str = greet("Alice")
    assert r1 == "hello Alice", "with name"
    r2: str = greet(None)
    assert r2 == "hello stranger", "without name"

test_optional_param()
