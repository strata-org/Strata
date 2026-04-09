class Data:
    x: int

    def __init__(self, x: int):
        self.x = x

def read_data(d: Data) -> int:
    return d.x

def test_oop_object_as_param():
    d = Data(42)
    r: int = read_data(d)
    assert r == 42, "object passed to function"

test_oop_object_as_param()
