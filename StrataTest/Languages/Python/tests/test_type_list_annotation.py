from typing import List

def test_type_list_annotation():
    xs: List[int] = [1, 2, 3]
    assert xs[0] == 1, "typed list"

test_type_list_annotation()
