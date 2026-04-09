def is_positive(x: int) -> bool:
    return x > 0

def test_func_bool_return():
    assert is_positive(5), "positive"
    assert not is_positive(-1), "negative"

test_func_bool_return()
