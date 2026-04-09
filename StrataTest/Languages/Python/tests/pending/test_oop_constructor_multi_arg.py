class Point:
    x: int
    y: int

    def __init__(self, x: int, y: int):
        self.x = x
        self.y = y

def test_oop_constructor_multi_arg():
    p = Point(3, 4)
    assert p.x == 3, "x field"
    assert p.y == 4, "y field"

test_oop_constructor_multi_arg()
