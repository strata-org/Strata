# Soundness bug: list aliasing - mutation through alias not visible
# Python lists are mutable reference objects. Assigning b = a creates
# an alias, not a copy. Strata treats assignment as value copy.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    a: list = [1, 2, 3]
    b: list = a
    b[0] = 99
    assert a[0] == 1, "unsound: Python gives 99"
test()
