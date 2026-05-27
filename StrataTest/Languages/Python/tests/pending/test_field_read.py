class Pair:
    a: int
    b: int

    def __init__(self, a: int, b: int):
        self.a = a
        self.b = b

def test_oop_field_read():
    p = Pair(10, 20)
    x: int = p.a
    y: int = p.b
    assert x == 10, "read a"
    assert y == 20, "read b"

test_oop_field_read()
