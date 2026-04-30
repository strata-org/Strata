def get_five() -> int:
    return 5

def test_func_no_args():
    assert get_five() == 5, "no args"

test_func_no_args()
