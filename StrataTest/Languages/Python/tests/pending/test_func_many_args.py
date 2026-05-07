def sum5(a: int, b: int, c: int, d: int, e: int) -> int:
    return a + b + c + d + e

def test_func_many_args():
    assert sum5(1, 2, 3, 4, 5) == 15, "five args"

test_func_many_args()
