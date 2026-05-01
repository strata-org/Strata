# strata-pending: soundness
# Soundness bug: ternary expression returns alias, not copy
# c = a if True else b makes c an alias of a. Mutating c mutates a.
# Strata treats the ternary result as an independent value.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    a: list = [1, 2]
    b: list = [3, 4]
    c: list = a if True else b
    c[0] = 99
    assert a[0] == 1, "unsound: Python gives 99"
test()
