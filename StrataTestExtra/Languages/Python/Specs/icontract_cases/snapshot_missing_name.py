# @snapshot without name= is a hard error.
import icontract


class C:
    x: int

    @icontract.snapshot(lambda self: self.x)
    def m(self) -> None:
        ...
