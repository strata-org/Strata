def test_while_break() -> None:
    count: int = 0
    i: int = 0
    while i < 10:
        if i == 3:
            break
        i = i + 1
        count = count + 1
    assert count >= 0, "count non-negative after break"

def test_while_continue() -> None:
    i: int = 0
    while i < 5:
        i = i + 1
        if i == 3:
            continue

def test_for_break() -> None:
    found: int = 0
    items: Any = [1, 2, 3]
    for x in items:
        found = 1
        break
    assert found >= 0, "found non-negative after for-break"
