class Registry:
    entries: dict

    def __init__(self):
        self.entries = {}

    def register(self, key: str, val: int):
        self.entries[key] = val

def test_oop_class_with_dict_field():
    r = Registry()
    r.register("a", 1)
    r.register("b", 2)
    assert r.entries["a"] == 1, "first entry"
    assert r.entries["b"] == 2, "second entry"

test_oop_class_with_dict_field()
