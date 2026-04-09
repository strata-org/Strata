def test_while_break():
    i: int = 0
    while i < 100:
        if i == 5:
            break
        i = i + 1
    assert i == 5, "while break"

test_while_break()
