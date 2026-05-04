# strata-args: --check-mode bugFinding --check-level full
class WithInit:
    x: int

    def __init__(self, x: int):
        self.x = x

class NoInit:
    y: int = 42

def test():
    a = WithInit(10)
    assert a.x == 10, "class with init"
    b = NoInit()
    # Previously this passed because Python was incorrectly creating Laurel procedures that were not modifying the heap.
    # For this to pass, we need transparent procedures with assignment in Laurel, so
    # NoInit.__init__ can be transparent instead of "opaque modifies *"
    assert a.x == 10, "class with init" 
test()
