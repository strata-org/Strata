class Square:
    side: int
    area: int

    def __init__(self, side: int):
        self.side = side
        self.area = side * side

def test_oop_constructor_computed_field():
    s = Square(5)
    assert s.side == 5, "side"
    assert s.area == 25, "computed area"

test_oop_constructor_computed_field()
