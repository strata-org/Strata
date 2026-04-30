# Soundness bug: augmented element assignment through alias
# b[0] = b[0] + 5 modifies the shared list. Since b is an alias of a,
# a[0] changes from 10 to 15. Strata treats b as an independent copy.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    a: list = [10, 20]
    b: list = a
    b[0] = b[0] + 5
    assert a[0] == 10, "unsound: Python gives 15"
test()
