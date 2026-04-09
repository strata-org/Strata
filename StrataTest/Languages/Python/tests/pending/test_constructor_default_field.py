class Counter:
    count: int

    def __init__(self):
        self.count = 0

def test_oop_constructor_default_field():
    c = Counter()
    assert c.count == 0, "default field value"

test_oop_constructor_default_field()
