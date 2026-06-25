def test_accumulator_pattern():
    items = [3, 1, 4, 1, 5]
    mx: int = items[0]
    for x in items:
        if x > mx:
            mx = x
    assert mx == 5, "find max"

test_accumulator_pattern()
