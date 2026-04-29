class Counter:
    val: int

    def __init__(self):
        self.val = 0

    def inc(self):
        self.val = self.val + 1

    def reset(self):
        self.val = 0

def test_class_counter_reset():
    c = Counter()
    c.inc()
    c.inc()
    c.reset()
    assert c.val == 0, "reset"

test_class_counter_reset()
