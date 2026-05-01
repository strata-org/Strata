# strata-pending: soundness
# Soundness bug: augmented modulo with negative divisor
# Python: 7 %= -3 gives -2 (sign follows divisor)
# Strata incorrectly computes 1 (Euclidean mod)
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    x: int = 7
    x %= -3
    assert x == 1, "unsound: Python gives -2"
test()
