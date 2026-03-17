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

    # F-string basics: variable interpolation, multiple parts, surrounding literals
    name: str = "world"
    tag: str = "ok"
    greeting: str = f"hello {name}, status=[{tag}]"
    assert greeting == "hello world, status=[ok]", "f-string interpolation failed"

    # F-string edge cases: empty, no interpolation, integer expression
    x: int = 3
    y: int = 4
    msg: str = f"{x} + {y}"
    empty: str = f""
    assert empty == "", "empty f-string failed"
    plain: str = f"literal only"
    assert plain == "literal only", "f-string no interpolation failed"

if __name__ == "__main__":
    main()
