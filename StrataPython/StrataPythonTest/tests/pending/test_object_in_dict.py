class Entry:
    val: int

    def __init__(self, val: int):
        self.val = val

def test_oop_object_in_dict():
    e = Entry(42)
    d = {"key": e}
    assert d["key"].val == 42, "object in dict"

test_oop_object_in_dict()
