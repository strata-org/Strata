# Single @invariant on a class. `self.x` resolves via the class field map.
import icontract


@icontract.invariant(lambda self: self.x >= 0)
class C:
    x: int

    def step(self) -> None:
        ...
