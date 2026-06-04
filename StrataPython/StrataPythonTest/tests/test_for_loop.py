def test_for_sum() -> Any:
    items: Any = [1, 2, 3, 4, 5]
    total: int = 0
    for x in items:
        total = total + x
    assert total == 15, "sum of list should be 15"
    return total

def test_for_with_conditional() -> Any:
    items: Any = [1, 2, 3, 4, 5, 6]
    count: int = 0
    for x in items:
        if x > 3:
            count = count + 1
    assert count == 3, "should count 3 items greater than 3"
    return count

def test_for_with_break() -> Any:
    items: Any = [10, 20, 30, 40, 50]
    found: int = 0
    for x in items:
        if x == 30:
            found = 1
            break
    assert found == 1, "should have found 30"
    return found
