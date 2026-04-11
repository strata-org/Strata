def test_for_break():
    items = [1, 2, 3, 4, 5]
    last: int = 0
    for x in items:
        if x == 3:
            break
        last = x
    assert last == 2, "for break"

test_for_break()
