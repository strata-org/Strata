class WithMethod:
    x: int = 10

    def get_x(self) -> int:
        return self.x

def test():
    w = WithMethod()
    assert True, "class with method but no __init__"
test()
