def test_count_pattern():
    items = [1, 2, 3, 2, 1, 2]
    count: int = 0
    for x in items:
        if x == 2:
            count = count + 1
    assert count == 3, "count occurrences"

test_count_pattern()
