# @ensure on __init__ produces a postcondition on the constructor.
import icontract


class C:
    x: int

    @icontract.ensure(lambda self: self.x >= 0)
    def __init__(self) -> None:
        ...
