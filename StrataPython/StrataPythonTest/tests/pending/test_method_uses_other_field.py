class Rect:
    w: int
    h: int

    def __init__(self, w: int, h: int):
        self.w = w
        self.h = h

    def area(self) -> int:
        return self.w * self.h

    def perimeter(self) -> int:
        return 2 * (self.w + self.h)

def test_oop_method_uses_other_field():
    r = Rect(3, 4)
    a: int = r.area()
    p: int = r.perimeter()
    assert a == 12, "area"
    assert p == 14, "perimeter"

test_oop_method_uses_other_field()
