def main():
    # String concatenation
    s1: str = "hello"
    s2: str = " world"
    result: str = s1 + s2
    assert result == "hello world", "string concatenation implemented incorrectly"
    
    # String comparison
    a: str = "abc"
    b: str = "abc"
    assert a == b, "string equality implemented incorrectly"

if __name__ == "__main__":
    main()
