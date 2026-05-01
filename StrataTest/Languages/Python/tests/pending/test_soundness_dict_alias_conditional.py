# strata-pending: soundness
# Soundness bug: dict mutation through alias after reading a value
# ref is an alias of original. Reading ref["a"] and then writing
# ref["b"] modifies original. Strata treats ref as an independent copy.
# This assertion is FALSE in Python but Strata verifies it as valid.
def test() -> None:
    original: dict = {"a": 1, "b": 2}
    ref: dict = original
    if ref["a"] == 1:
        ref["b"] = 99
    assert original["b"] == 2, "unsound: Python gives 99"
test()
