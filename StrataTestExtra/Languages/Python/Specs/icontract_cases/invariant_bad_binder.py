# @invariant binder must be `self`; non-`self` binders are skipped with a warning.
import icontract


@icontract.invariant(lambda obj: obj.x >= 0)
class C:
    x: int
