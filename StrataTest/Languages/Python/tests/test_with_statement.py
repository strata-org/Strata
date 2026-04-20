# strata-args: --check-mode bugFinding --check-level full
class Resource:
    def __init__(self, n: int):
        self.value : int = n

    def __enter__(self) -> int:
        return self.value

    def __exit__(self) -> bool:
        return True

    def get_value(self) -> int:
        return self.value

def test_with_as():
    res: Resource = Resource(42)
    result: int = 0
    with res as val:
        result = val
    assert result == 42

def test_with_no_as():
    res: Resource = Resource(10)
    with res:
        x: int = res.get_value()
        assert x == 10

def test_with_multiple():
    r1: Resource = Resource(1)
    r2: Resource = Resource(2)
    with r1 as a, r2 as b:
        total: int = a + b
        assert total == 3
