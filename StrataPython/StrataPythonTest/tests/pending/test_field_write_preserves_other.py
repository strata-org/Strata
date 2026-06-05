class Pair:
    a: int
    b: int

    def __init__(self, a: int, b: int):
        self.a = a
        self.b = b

def test_oop_field_write_preserves_other():
    p = Pair(1, 2)
    p.a = 99
    assert p.a == 99, "a updated"
    assert p.b == 2, "b unchanged"

test_oop_field_write_preserves_other()
