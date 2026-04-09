class Item:
    v: int

    def __init__(self, v: int):
        self.v = v

def test_list_of_objects():
    items = [Item(1), Item(2), Item(3)]
    s: int = 0
    for it in items:
        s = s + it.v
    assert s == 6, "sum object fields"

test_list_of_objects()
