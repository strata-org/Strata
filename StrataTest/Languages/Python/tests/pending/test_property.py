class Circle:
    _radius: int

    def __init__(self, radius: int):
        self._radius = radius

    @property
    def radius(self) -> int:
        return self._radius

def test():
    c = Circle(5)
    assert c.radius == 5, "property"
test()
