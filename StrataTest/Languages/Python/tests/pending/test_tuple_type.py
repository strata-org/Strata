from typing import Tuple

def test():
    t: Tuple[int, str] = (1, "hello")
    assert t[0] == 1, "typed tuple"
test()
