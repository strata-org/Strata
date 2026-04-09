class Counter:
    val: int

    def __init__(self):
        self.val = 0

    def inc(self):
        self.val = self.val + 1

def test_class_method():
    c = Counter()
    c.inc()
    c.inc()
    assert c.val == 2, "method call"

test_class_method()
