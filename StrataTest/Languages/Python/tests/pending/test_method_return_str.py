class Tag:
    label: str

    def __init__(self, label: str):
        self.label = label

    def get_label(self) -> str:
        return self.label

def test_oop_method_return_str():
    t = Tag("important")
    r: str = t.get_label()
    assert r == "important", "method returns str"

test_oop_method_return_str()
