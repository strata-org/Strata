# Duplicate snapshot name= within one method is a hard error.
import icontract


class C:
    x: int

    @icontract.snapshot(lambda self: self.x, name="v")
    @icontract.snapshot(lambda self: self.x, name="v")
    def m(self) -> None:
        ...
