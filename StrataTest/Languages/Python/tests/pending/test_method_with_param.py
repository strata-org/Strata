class Adder:
    base: int

    def __init__(self, base: int):
        self.base = base

    def add(self, x: int) -> int:
        return self.base + x

def test_oop_method_with_param():
    a = Adder(100)
    r: int = a.add(5)
    assert r == 105, "method with param"

test_oop_method_with_param()
