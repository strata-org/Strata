def test_flag_found():
    items = [1, 2, 3]
    has_even: bool = False
    for x in items:
        if x % 2 == 0:
            has_even = True
    assert has_even, "found even"

test_flag_found()
