# Soundness bug: dict mutation through function parameter
# Python passes mutable objects by reference. Modifying d inside
# modify() should be visible to the caller. Strata doesn't model this.
# This assertion is FALSE in Python but Strata verifies it as valid.
def modify(d: dict) -> None:
    d["key"] = 99

def test() -> None:
    a: dict = {"key": 1}
    modify(a)
    assert a["key"] == 1, "unsound: Python gives 99"
test()
