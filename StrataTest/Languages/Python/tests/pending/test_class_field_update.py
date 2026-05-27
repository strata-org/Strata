class Pair:
    a: int
    b: int

    def __init__(self, a: int, b: int):
        self.a = a
        self.b = b

def test_class_field_update():
    p = Pair(1, 2)
    p.a = 10
    assert p.a == 10, "field update"
    assert p.b == 2, "other field unchanged"

test_class_field_update()
