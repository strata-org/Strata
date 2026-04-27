import servicelib

class Counter:
    def __init__(self, start: int):
        self.value: int = start

    def increment(self) -> int:
        self.value = self.value + 1
        return self.value

def use_counter() -> int:
    c: Counter = Counter(10)
    result: int = c.increment()
    return result
