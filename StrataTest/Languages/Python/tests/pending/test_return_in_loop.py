def first_positive(xs) -> int:
    for x in xs:
        if x > 0:
            return x
    return -1

def test_return_in_loop():
    assert first_positive([-1, -2, 3, 4]) == 3, "return in loop"
    assert first_positive([-1, -2]) == -1, "no positive"

test_return_in_loop()
