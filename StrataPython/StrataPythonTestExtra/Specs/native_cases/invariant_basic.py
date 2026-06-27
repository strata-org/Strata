# Native @invariant class decorator.
@invariant(lambda self: self.x >= 0)
class C:
    x: int

    def step(self) -> None:
        ...
