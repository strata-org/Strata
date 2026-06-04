class MathHelper:
    @staticmethod
    def add(a: int, b: int) -> int:
        return a + b

def test():
    r: int = MathHelper.add(3, 4)
    assert r == 7, "static method"
test()
