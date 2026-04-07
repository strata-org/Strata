def test_list_sum():
    xs = [10, -3, 7, -4]
    s: int = 0
    for x in xs:
        s += x
    assert s == 10, "list sum with negatives and augmented assign"

test_list_sum()
