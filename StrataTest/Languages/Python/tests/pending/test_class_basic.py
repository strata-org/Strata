class Point:
    x: int
    y: int

    def __init__(self, x: int, y: int):
        self.x = x
        self.y = y

def test_class_basic():
    p = Point(3, 4)
    assert p.x == 3, "field x"
    assert p.y == 4, "field y"

test_class_basic()
