from typing import List

def test():
    xs: List[List[int]] = [[1, 2], [3, 4]]
    assert xs[0][0] == 1, "list of list"
test()
