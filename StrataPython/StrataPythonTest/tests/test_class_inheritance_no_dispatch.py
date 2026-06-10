# Test that classes involved in inheritance have their method calls
# conservatively lowered as holes (not statically resolved), since
# dynamic dispatch could call a different method at runtime.
# The assert inside Child.value() should NOT be reachable from main,
# because the call obj.value() is a hole (obj's static type Base
# could hold a Child at runtime).

class Base:
    def __init__(self) -> None:
        self.x: int = 0

    def value(self) -> int:
        return self.x

class Child(Base):
    def __init__(self) -> None:
        self.x: int = 42

    def value(self) -> int:
        assert False, "should not be analyzed"
        return self.x

if __name__ == "__main__":
    obj: Base = Base()
    result: int = obj.value()
