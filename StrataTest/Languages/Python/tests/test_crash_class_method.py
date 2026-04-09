class Counter:
    count: int = 0

    @classmethod
    def increment(cls):
        cls.count = cls.count + 1

def test():
    Counter.increment()
    assert Counter.count == 1, "class method"
test()
