class Item:
    v: int

    def __init__(self, v: int):
        self.v = v

def test_oop_object_in_list():
    a = Item(10)
    b = Item(20)
    items = [a, b]
    assert items[0].v == 10, "first object"
    assert items[1].v == 20, "second object"

test_oop_object_in_list()
