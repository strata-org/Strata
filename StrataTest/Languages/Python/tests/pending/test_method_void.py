class Acc:
    val: int

    def __init__(self):
        self.val = 0

    def inc(self):
        self.val = self.val + 1

def test_oop_method_void():
    a = Acc()
    a.inc()
    a.inc()
    a.inc()
    assert a.val == 3, "three increments"

test_oop_method_void()
