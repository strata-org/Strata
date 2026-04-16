class Counter:
    def __init__(self) -> None:
        self.count: int = 0

    def next(self) -> int:
        self.count = self.count + 1
        return self.count

def test():
    c: Counter = Counter()
    a = b = c.next()
    assert a == 1, "a should be 1"
    assert b == 1, "b should be 1"
    assert c.count == 1, "next() called exactly once"

test()
