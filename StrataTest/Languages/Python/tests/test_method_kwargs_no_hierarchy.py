class Calculator:
    def __init__(self, base: int) -> None:
        self.base: int = base

    def add(self, x: int, y: int = 0) -> int:
        return self.base + x + y

def main() -> None:
    c: Calculator = Calculator(10)
    d: dict = {"y": 5}
    result: int = c.add(1, **d)
    assert result == 16
