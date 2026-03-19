def test_while_break() -> None:
    done: bool = False
    while not done:
        break

def test_while_continue() -> None:
    done: bool = False
    while not done:
        done = True
        continue

def test_for_break() -> None:
    items: Any = [1, 2, 3]
    for x in items:
        break

def test_for_continue() -> None:
    items: Any = [1, 2, 3]
    for x in items:
        continue
