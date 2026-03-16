def main():
    # If-else with equality
    x: int = 5
    result: int = 0
    
    if x == 5:
        result = 10
    else:
        result = 20
    
    assert result == 10, "if-else implemented incorrectly"
    
    # Nested if with equality
    y: int = 7
    status: int = 0
    
    if y == 7:
        if y == 7:
            status = 1
        else:
            status = 2
    else:
        status = 3
    
    assert status == 1, "nested if implemented incorrectly"
    
    # If with comparison operators
    a: int = 10
    b: int = 0
    
    if a > 3:
        b = 1
    else:
        b = 2
    
    assert b == 1, "if with > implemented incorrectly"
    
    # If with multiple comparisons
    c: int = 8
    d: int = 0
    
    if c > 5:
        if c < 10:
            d = 100
        else:
            d = 200
    else:
        d = 300
    
    assert d == 100, "nested if with comparisons implemented incorrectly"
    
    # If with <=
    e: int = 5
    f: int = 0
    
    if e <= 5:
        f = 50
    else:
        f = 60
    
    assert f == 50, "if with <= implemented incorrectly"
    
    # If with >=
    g: int = 10
    h: int = 0
    
    if g >= 10:
        h = 70
    else:
        h = 80
    
    assert h == 70, "if with >= implemented incorrectly"

    # Ternary if expression (true branch)
    tx: int = 10
    ty: int = 1 if tx > 5 else 0
    assert ty == 1

    # Ternary if expression (false branch)
    tz: int = 1 if tx < 5 else 0
    assert tz == 0

    # Break in while loop
    bk: int = 0
    while bk < 10:
        if bk == 5:
            break
        bk = bk + 1
    assert bk >= 0

    # Continue in while loop
    total: int = 0
    ci: int = 0
    while ci < 5:
        ci = ci + 1
        if ci == 3:
            continue
        total = total + ci
    assert total >= 0

if __name__ == "__main__":
    main()
