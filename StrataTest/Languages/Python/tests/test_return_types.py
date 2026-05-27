def get_number() -> int:
    return 42

def get_greeting() -> str:
    return "hello"

def get_flag() -> bool:
    return True

def get_nothing() -> None:
    x: int = 1
    return None

def add(a: int, b: int) -> int:
    result: int = a + b
    return result

def main():
    n: int = get_number()
    assert n == 42, "get_number returned wrong value"

    s: str = get_greeting()
    assert s == "hello", "get_greeting returned wrong value"

    b: bool = get_flag()
    assert b == True, "get_flag returned wrong value"

    total: int = add(10, 20)
    assert total == 30, "add returned wrong value"

if __name__ == "__main__":
    main()
