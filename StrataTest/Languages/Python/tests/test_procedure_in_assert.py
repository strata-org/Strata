from datetime import timedelta

def main() -> int:
    # Nesting a multi-output procedure call (timedelta_func) inside a
    # binary expression generates an exception assertion containing the
    # procedure call. Without hoisting, this causes:
    # "calls to procedures are not supported in functions or contracts"
    base: int = 100
    delta: Any = base - timedelta(days=7)
    result: int = 1
    assert result == 1, "should pass"
    return result

if __name__ == "__main__":
    main()
