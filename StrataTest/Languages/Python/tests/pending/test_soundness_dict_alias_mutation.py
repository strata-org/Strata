# strata-pending: soundness
# Soundness bug: dict aliasing - mutation through alias not visible
# Python dicts are mutable reference objects. Assigning b = a creates
# an alias, not a copy. Strata treats assignment as value copy.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    a: dict = {"x": 1}
    b: dict = a
    b["x"] = 99
    assert a["x"] == 1, "unsound: Python gives 99"
test()
