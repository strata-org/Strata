def greet(name: str, greeting: str = "Hello") -> str:
    result: str = greeting + " " + name
    return result

def power(base: int, exp: int = 2) -> int:
    result: int = 1
    i: int = 0
    while i < exp:
        result = result * base
        i = i + 1
    return result

def main():
    msg1: str = greet("Alice")
    assert msg1 == "Hello Alice", "default greeting failed"

    msg2: str = greet("Bob", "Hi")
    assert msg2 == "Hi Bob", "explicit greeting failed"

    sq: int = power(3)
    assert sq == 9, "default power failed"

    cu: int = power(2, 3)
    assert cu == 8, "explicit power failed"

if __name__ == "__main__":
    main()
