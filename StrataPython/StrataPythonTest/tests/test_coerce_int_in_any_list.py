from typing import Any, List

def test_coerce_int_in_any_list():
    xs: List[Any] = [1, "two", 3]
    assert xs[0] == 1, "int in Any list"
    assert xs[1] == "two", "str in Any list"

test_coerce_int_in_any_list()
