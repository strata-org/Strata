class Box:
    val: int

    def __init__(self, val: int):
        self.val = val

def test_oop_object_reassign():
    b = Box(1)
    b = Box(2)
    assert b.val == 2, "reassigned to new object"

test_oop_object_reassign()
