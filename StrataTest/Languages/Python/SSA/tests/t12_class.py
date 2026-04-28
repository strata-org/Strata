# Test: ClassDef, @ClassName_init, methods with self

class Point:
    dimensions: int = 2

    def __init__(self, x: int, y: int):
        self.x = x
        self.y = y

    def distance(self) -> int:
        return self.x + self.y

p = Point(3, 4)
d = p.distance()
