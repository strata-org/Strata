import servicelib

class Counter:
    def __init__(self, start: int):
        self.value: int = start

    def get_value(self) -> int:
        return self.value

def use_counter() -> int:
    c: Counter = Counter(0)
    return c.get_value()
