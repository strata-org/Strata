def main():
    # Equality (supported for all types)
    a: int = 10
    b: int = 10
    assert a == b, "equality implemented incorrectly"
    
    s1: str = "test"
    s2: str = "test"
    assert s1 == s2, "string equality implemented incorrectly"
    
    # Comparison operators for integers
    x: int = 5
    y: int = 3
    assert x > y, "greater than implemented incorrectly"
    assert y < x, "less than implemented incorrectly"
    assert x >= 5, "greater than or equal implemented incorrectly"
    assert y <= 3, "less than or equal implemented incorrectly"

if __name__ == "__main__":
    main()
