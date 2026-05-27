def main():
    # Integer multiplication
    x: int = 5
    y: int = 3
    
    prod: int = x * y
    assert prod == 15, "multiplication implemented incorrectly"
    
    a: int = 10
    b: int = 2
    result: int = a * b
    assert result == 20, "multiplication implemented incorrectly"
    
    # Integer addition
    sum_val: int = x + y
    assert sum_val == 8, "addition implemented incorrectly"
    
    # Integer subtraction
    diff: int = x - y
    assert diff == 2, "subtraction implemented incorrectly"
    
    # Floor division
    quot: int = a // b
    assert quot == 5, "floor division implemented incorrectly"

    # Mod
    rem: int = x % y
    assert rem == 2, "mod implemented incorrectly"

    # Negative Mod
    neg_rem1: int = (-7) % 3
    assert neg_rem1 == 2, "negative mod should follow Python floored semantics"

if __name__ == "__main__":
    main()
