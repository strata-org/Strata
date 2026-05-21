# Stacked @snapshot decorators with distinct name= are all captured.
import icontract


class C:
    x: int
    y: int

    @icontract.snapshot(lambda self: self.x, name="x0")
    @icontract.snapshot(lambda self: self.y, name="y0")
    def step(self) -> None:
        ...
