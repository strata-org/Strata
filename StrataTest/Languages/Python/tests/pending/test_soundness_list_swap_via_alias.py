# Soundness bug: list swap through alias shows both directions of aliasing
# Modifying b[0] changes a[0] AND modifying b[2] changes a[2].
# Strata treats b as an independent copy, so a is unchanged.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    a: list = [10, 20, 30]
    b: list = a
    b[0] = 30
    b[2] = 10
    assert a[0] == 10, "unsound: Python gives 30"
test()
