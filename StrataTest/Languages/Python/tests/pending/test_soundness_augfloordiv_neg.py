# strata-pending: soundness
# Soundness bug: augmented floor division with negative divisor
# Python: 7 //= -2 gives -4
# Strata incorrectly computes -3 (Euclidean division)
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    x: int = 7
    x //= -2
    assert x == -3, "unsound: Python gives -4"
test()
