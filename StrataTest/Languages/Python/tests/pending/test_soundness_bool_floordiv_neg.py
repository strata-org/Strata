# Soundness bug: bool floor division with negative divisor
# Python: True // (-3) = 1 // (-3) = -1 (floor of -0.333...)
# Strata incorrectly computes 0 (Euclidean: 1 div (-3) = 0)
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    x: int = True // (-3)
    assert x == 0, "unsound: Python gives -1"
test()
