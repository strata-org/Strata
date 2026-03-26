def test_while_countdown() -> int:
    n: int = 5
    total: int = 0
    while n > 0:
        total = total + n
        n = n - 1
    assert total == 15, "countdown sum should be 15"
    return total

def test_while_true_break() -> int:
    count: int = 0
    while True:
        count = count + 1
        if count == 10:
            break
    assert count == 10, "should have counted to 10"
    return count

def test_while_with_continue() -> int:
    i: int = 0
    total: int = 0
    while i < 10:
        i = i + 1
        if i == 5:
            continue
        total = total + i
    assert total == 50, "sum excluding 5 should be 50"
    return total
