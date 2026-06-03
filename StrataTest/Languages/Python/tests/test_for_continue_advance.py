def test_for_continue_advance() -> None:
    items: Any = [1, 2, 3]
    s: int = 0
    for x in items:
        if x == 2:
            continue
        s = s + x

test_for_continue_advance()
