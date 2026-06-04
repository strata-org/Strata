# strata-pending: soundness
# Soundness bug: chain of aliases - mutation through transitive alias
# a, b, c all refer to the same dict. Mutating through c should be
# visible through a. Strata treats each assignment as a value copy.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    a: dict = {"x": 1}
    b: dict = a
    c: dict = b
    c["x"] = 99
    assert a["x"] == 1, "unsound: Python gives 99"
test()
