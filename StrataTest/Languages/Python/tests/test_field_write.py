class Cell:
    val: int

    def __init__(self, val: int):
        self.val = val

def test_oop_field_write():
    c = Cell(1)
    c.val = 99
    assert c.val == 99, "field overwritten"

test_oop_field_write()
