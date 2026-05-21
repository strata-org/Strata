# @ensure referencing a declared @snapshot via OLD.<name>.
import icontract


class C:
    x: int

    @icontract.snapshot(lambda self: self.x, name="v0")
    @icontract.ensure(lambda OLD: OLD.v0 >= 0)
    def grow(self) -> None:
        ...
