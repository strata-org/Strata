def my_abs(x: int) -> int:
    if x < 0:
        return -x
    return x

def test_abs_manual():
    assert my_abs(-5) == 5, "abs negative"
    assert my_abs(0) == 0, "abs zero"
    assert my_abs(3) == 3, "abs positive"

test_abs_manual()
