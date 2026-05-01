# strata-pending: soundness
# Soundness bug: nested list mutation through shared reference
# inner is stored in outer. Mutating outer[0][0] should change inner[0]
# because they are the same object. Strata doesn't model this sharing.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    inner: list = [1, 2]
    outer: list = [inner]
    outer[0][0] = 99
    assert inner[0] == 1, "unsound: Python gives 99"
test()
