def abs_val(x: int) -> int:
    if x < 0:
        return -x
    return x

def test_return_early():
    assert abs_val(-3) == 3, "early return negative"
    assert abs_val(5) == 5, "no early return"

test_return_early()
