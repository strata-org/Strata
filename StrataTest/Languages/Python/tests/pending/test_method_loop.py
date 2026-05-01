class Summer:
    total: int

    def __init__(self):
        self.total = 0

    def add_range(self, n: int):
        i: int = 0
        while i < n:
            self.total = self.total + i
            i = i + 1

def test_oop_method_loop():
    s = Summer()
    s.add_range(5)
    assert s.total == 10, "sum 0..4"

test_oop_method_loop()
