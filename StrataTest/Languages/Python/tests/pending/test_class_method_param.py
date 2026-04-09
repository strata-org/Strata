class Adder:
    base: int

    def __init__(self, base: int):
        self.base = base

    def add(self, x: int) -> int:
        return self.base + x

def test_class_method_param():
    a = Adder(10)
    assert a.add(5) == 15, "method with param"

test_class_method_param()
