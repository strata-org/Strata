# Soundness bug: list mutation in conditional branch through alias
# Even when mutation happens inside a conditional, the alias relationship
# means the original list is modified. Strata doesn't track this.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    a: list = [1, 2, 3]
    b: list = a
    if True:
        b[0] = 99
    assert a[0] == 1, "unsound: Python gives 99"
test()
