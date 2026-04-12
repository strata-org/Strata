class Box:
    v: int

    def __init__(self, v: int):
        self.v = v

    def get(self) -> int:
        return self.v

def test_oop_method_return_int():
    b = Box(10)
    r: int = b.get()
    assert r == 10, "method returns int"

test_oop_method_return_int()
