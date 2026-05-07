from typing import Union

def test():
    x: Union[int, str] = 42
    assert x == 42, "union type"
test()
