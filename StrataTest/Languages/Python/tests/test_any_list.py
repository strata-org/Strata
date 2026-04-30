from typing import Any

def test_any_list():
    x: Any = [1, 2, 3]
    assert x[0] == 1, "Any holds list"

test_any_list()
