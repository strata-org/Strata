# Soundness bug: floor division with negative divisor uses Euclidean division
# Python: 7 // (-2) == -4 (floor toward -inf)
# Strata incorrectly computes -3 (Euclidean division, rounds toward zero)
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    x: int = 7 // (-2)
    assert x == -3, "unsound: Python gives -4"
test()
