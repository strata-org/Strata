class Gate:
    open: bool

    def __init__(self):
        self.open = False

    def is_open(self) -> bool:
        return self.open

    def toggle(self):
        self.open = not self.open

def test_oop_method_return_bool():
    g = Gate()
    r1: bool = g.is_open()
    assert r1 == False, "initially closed"
    g.toggle()
    r2: bool = g.is_open()
    assert r2 == True, "toggled open"

test_oop_method_return_bool()
