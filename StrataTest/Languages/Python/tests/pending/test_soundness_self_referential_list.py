# strata-pending: soundness
# Soundness bug: self-referential list structure
# a[1] = a makes the list contain itself. Mutating a[0] is visible
# through a[1][0] since a[1] IS a. Strata copies the value instead.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    a: list = [1, 2]
    a[1] = a
    a[0] = 99
    assert a[1][0] == 1, "unsound: Python gives 99"
test()
