# strata-pending: soundness
# Soundness bug: function returning its argument creates alias
# identity() returns the same object it received. b is an alias of a.
# Mutating b mutates a. Strata treats the return value as a fresh copy.
# This assertion is FALSE in Python but Strata verifies it as valid.
def identity(x: list) -> list:
    return x

def test() -> None:
    a: list = [1, 2, 3]
    b: list = identity(a)
    b[0] = 99
    assert a[0] == 1, "unsound: Python gives 99"
test()
