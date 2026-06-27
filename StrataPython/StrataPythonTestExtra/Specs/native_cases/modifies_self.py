# @modifies IS allowed to reference self.x (field access enabled for the
# not-yet-lowered targets); the target is recognized as getIndex(self, "x").
class C:
    x: int

    @modifies(lambda self: self.x)
    def m(self) -> None:
        ...
