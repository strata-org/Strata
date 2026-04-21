def greet(name: str, greeting: str = "Hello", **kwargs) -> str:
    name = greeting + " " + name
    return name

def test_kwargs():
    r1: str = greet("Alice", greeting="Hi")
    assert r1 == "Hi Alice", "kwargs call"

test_kwargs()
