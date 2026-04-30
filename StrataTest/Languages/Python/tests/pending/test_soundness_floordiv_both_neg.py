# Soundness bug: floor division with both operands negative
# Python: (-7) // (-2) == 3 (floor of 3.5)
# Strata incorrectly computes 4 (Euclidean division)
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    x: int = (-7) // (-2)
    assert x == 4, "unsound: Python gives 3"
test()
