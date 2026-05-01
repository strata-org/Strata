# strata-pending: soundness
# Soundness bug: Python's mod result sign follows divisor sign
# Python: 10 % (-3) == -2 (negative, like divisor)
# Strata incorrectly computes 1 (Euclidean mod, always non-negative)
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    x: int = 10 % (-3)
    assert x == 1, "unsound: Python gives -2"
test()
