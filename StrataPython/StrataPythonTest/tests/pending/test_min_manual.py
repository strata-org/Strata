def my_min(a: int, b: int) -> int:
    if a < b:
        return a
    return b

def test_min_manual():
    assert my_min(3, 7) == 3, "min first"
    assert my_min(9, 2) == 2, "min second"
    assert my_min(5, 5) == 5, "min equal"

test_min_manual()
