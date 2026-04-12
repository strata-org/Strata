# strata-args: --check-mode bugFinding --check-level full
class WithInit:
    x: int

    def __init__(self, x: int):
        self.x = x

class NoInit:
    y: int = 42

def test():
    a = WithInit(10)
    b = NoInit()
    assert a.x == 10, "class with init"
test()
