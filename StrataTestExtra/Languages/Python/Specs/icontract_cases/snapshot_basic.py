# @snapshot with name= captures a pre-state value.
import icontract


class C:
    x: int

    @icontract.snapshot(lambda self: self.x, name="v0")
    def m(self) -> None:
        ...
