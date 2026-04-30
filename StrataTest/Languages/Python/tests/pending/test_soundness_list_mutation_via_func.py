# Soundness bug: list mutation through function parameter
# Python passes mutable objects by reference. Modifying lst inside
# modify() should be visible to the caller. Strata doesn't model this.
# This assertion is FALSE in Python but Strata verifies it as valid.
def modify(lst: list) -> None:
    lst[0] = 99

def test() -> None:
    a: list = [1, 2, 3]
    modify(a)
    assert a[0] == 1, "unsound: Python gives 99"
test()
