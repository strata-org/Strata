def test_for_sum():
    items = [1, 2, 3, 4, 5]
    total: int = 0
    for x in items:
        total = total + x
    assert total == 15, "for loop sum"

test_for_sum()
