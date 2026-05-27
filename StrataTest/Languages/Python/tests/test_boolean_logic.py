def main():
    # Boolean and
    a: bool = True
    b: bool = False
    assert a and a, "True and True should be True"
    assert not (a and b), "True and False should be False"

    # Boolean or
    assert a or b, "True or False should be True"
    assert not (b or b), "False or False should be False"

    # Not
    assert not b, "not False should be True"
    assert not not a, "not not True should be True"

    # Combined conditions
    c: int = 10
    d: int = 20
    result: int = 0

    if c > 5 and d > 15:
        result = 1
    else:
        result = 0
    assert result == 1, "combined and condition failed"

    if c > 15 or d > 15:
        result = 2
    else:
        result = 0
    assert result == 2, "combined or condition failed"

    if not (c > 20):
        result = 3
    else:
        result = 0
    assert result == 3, "not condition failed"

if __name__ == "__main__":
    main()
