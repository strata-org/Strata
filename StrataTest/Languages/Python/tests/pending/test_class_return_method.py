class Box:
    v: int

    def __init__(self, v: int):
        self.v = v

    def get(self) -> int:
        return self.v

def test_class_return_method():
    b = Box(42)
    assert b.get() == 42, "method return"

test_class_return_method()
