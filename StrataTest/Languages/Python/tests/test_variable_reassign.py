def main():
    # Variable reassignment
    x: int = 1
    assert x == 1, "initial value"
    x = 2
    assert x == 2, "after reassignment"
    x = x + 3
    assert x == 5, "after increment"

    # Reassignment in loop
    total: int = 0
    i: int = 0
    while i < 5:
        total = total + i
        i = i + 1
    assert total == 10, "loop sum should be 10"

    # Conditional reassignment
    val: int = 0
    flag: bool = True
    if flag:
        val = 100
    else:
        val = 200
    assert val == 100, "should be 100"

    flag = False
    if flag:
        val = 100
    else:
        val = 200
    assert val == 200, "should be 200"

if __name__ == "__main__":
    main()
