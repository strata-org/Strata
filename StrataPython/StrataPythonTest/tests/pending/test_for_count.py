def test_for_count():
    items = [10, 20, 30, 40]
    count: int = 0
    for x in items:
        count = count + 1
    assert count == 4, "for loop count"

test_for_count()
