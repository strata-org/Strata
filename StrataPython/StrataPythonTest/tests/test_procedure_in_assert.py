from datetime import timedelta

def main() -> int:
    base: int = 100
    delta: Any = base - timedelta(days=7)
    result: int = 1
    assert result == 1, "should pass"
    return result

if __name__ == "__main__":
    main()
