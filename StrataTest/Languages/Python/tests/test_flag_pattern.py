def test_flag_pattern():
    items = [1, 3, 5, 7]
    has_even: bool = False
    for x in items:
        if x % 2 == 0:
            has_even = True
    assert not has_even, "no even numbers"

test_flag_pattern()
