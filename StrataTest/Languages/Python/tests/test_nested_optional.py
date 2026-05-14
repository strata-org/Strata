from typing import Optional, List

def test():
    x: Optional[List[int]] = [1, 2, 3]
    assert x[0] == 1, "nested optional list"
test()
