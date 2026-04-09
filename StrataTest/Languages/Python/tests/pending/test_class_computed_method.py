class Rect:
    w: int
    h: int

    def __init__(self, w: int, h: int):
        self.w = w
        self.h = h

    def area(self) -> int:
        return self.w * self.h

def test_class_computed_method():
    r = Rect(3, 4)
    assert r.area() == 12, "area"

test_class_computed_method()
