# `self.x` in @requires: field access is NOT enabled for the lowered contract
# kinds, so this predicate is unsupported (dropped with a warning) for now —
# lowering receiver-bound preconditions is deferred. Contrast @invariant, which
# IS allowed to reference self.x (it is recognized + round-tripped, not lowered).
class C:
    x: int

    @requires(lambda self: self.x >= 0)
    def m(self) -> None:
        ...
