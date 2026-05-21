# Stacked @invariant decorators produce multiple invariants.
import icontract


@icontract.invariant(lambda self: self.x >= 0)
@icontract.invariant(lambda self: self.y >= 0)
class C:
    x: int
    y: int

    def step(self) -> None:
        ...
