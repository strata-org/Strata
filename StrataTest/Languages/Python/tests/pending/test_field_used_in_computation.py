class Circle:
    radius: int

    def __init__(self, radius: int):
        self.radius = radius

    def diameter(self) -> int:
        return self.radius * 2

def test_oop_field_used_in_computation():
    c = Circle(5)
    d: int = c.diameter()
    assert d == 10, "diameter from radius"

test_oop_field_used_in_computation()
