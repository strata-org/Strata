value: int = 42

def get_value() -> int:
    global value
    return value

def main() -> None:
    result: int = get_value()
    assert result == 42
