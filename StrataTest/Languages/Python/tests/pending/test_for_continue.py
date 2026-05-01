def test_for_continue():
    items = [1, 2, 3, 4, 5]
    s: int = 0
    for x in items:
        if x == 3:
            continue
        s = s + x
    assert s == 12, "for continue skips 3"

test_for_continue()
