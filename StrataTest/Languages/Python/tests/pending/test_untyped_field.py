class Bag:
    def __init__(self, item):
        self.item = item

def test_untyped_field():
    b = Bag(42)
    assert b.item == 42, "untyped field"

test_untyped_field()
