class Calc:
    def __init__(self):
        pass

    def add(self, a: int, b: int) -> int:
        return a + b

def test_oop_method_multi_param():
    c = Calc()
    r: int = c.add(3, 7)
    assert r == 10, "method with two params"

test_oop_method_multi_param()
