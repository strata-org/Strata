class Data:
    x: int
    name: str
    def __init__(self, x: int, name: str):
        self.x = x
        self.name = name

class Container:
    data: Data
    count: int
    def __init__(self, data: Data, count: int):
        self.data = data
        self.count = count

def test_oop_mixed_field_types():
    """Class with both primitive and user-defined type fields"""
    d = Data(10, "hello")
    c = Container(d, 5)
    assert c.count == 5, "primitive field"
    assert c.data.x == 10, "nested object field"

test_oop_mixed_field_types()
