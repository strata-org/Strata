def my_max(a: int, b: int) -> int:
    if a > b:
        return a
    return b

def test_max_manual():
    assert my_max(3, 7) == 7, "max second"
    assert my_max(9, 2) == 9, "max first"

test_max_manual()
