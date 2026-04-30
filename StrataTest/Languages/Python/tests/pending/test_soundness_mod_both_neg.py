# Soundness bug: modulo with both operands negative
# Python: (-7) % (-2) == -1 (sign follows divisor)
# Strata incorrectly computes 1 (Euclidean mod, always non-negative)
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    x: int = (-7) % (-2)
    assert x == 1, "unsound: Python gives -1"
test()
