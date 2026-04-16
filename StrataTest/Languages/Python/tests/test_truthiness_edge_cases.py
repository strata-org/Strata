"""
Edge-case tests for Python truthiness semantics.

These document the exact Python behavior that the Strata runtime
(Any_to_bool, PNot, PAnd, POr) must model correctly.

Covers the gaps identified in issue #934:
  - bool(float) — missing from Any_to_bool
  - not None, not {} — missing from PNot
  - and/or with float, dict, list operands — missing from PAnd/POr requires
"""


# ---------------------------------------------------------------------------
# 1. bool() / truthiness — every type that Any_to_bool should handle
# ---------------------------------------------------------------------------

def test_bool_none():
    assert bool(None) == False

def test_bool_bool():
    assert bool(True) == True
    assert bool(False) == False

def test_bool_int():
    assert bool(0) == False
    assert bool(1) == True
    assert bool(-1) == True

def test_bool_float():
    """This is the case missing from Any_to_bool."""
    assert bool(0.0) == False
    assert bool(1.5) == True
    assert bool(-0.0) == False

def test_bool_str():
    assert bool("") == False
    assert bool("x") == True

def test_bool_list():
    assert bool([]) == False
    assert bool([1]) == True

def test_bool_dict():
    assert bool({}) == False
    assert bool({"a": 1}) == True


# ---------------------------------------------------------------------------
# 2. not — every type that PNot should handle
# ---------------------------------------------------------------------------

def test_not_none():
    """Missing from PNot — was returning exception."""
    assert (not None) == True

def test_not_bool():
    assert (not True) == False
    assert (not False) == True

def test_not_int():
    assert (not 0) == True
    assert (not 1) == False

def test_not_float():
    assert (not 0.0) == True
    assert (not 3.14) == False

def test_not_str():
    assert (not "") == True
    assert (not "hi") == False

def test_not_list():
    assert (not []) == True
    assert (not [1]) == False

def test_not_dict():
    """Missing from PNot — was returning exception."""
    assert (not {}) == True
    assert (not {"k": "v"}) == False


# ---------------------------------------------------------------------------
# 3. and — short-circuit: returns first falsy operand, or last operand
# ---------------------------------------------------------------------------

def test_and_bool():
    assert (True and True) == True
    assert (True and False) == False
    assert (False and True) == False

def test_and_none():
    assert (None and True) is None
    assert (None and 42) is None

def test_and_int():
    assert (0 and "hello") == 0
    assert (1 and "hello") == "hello"

def test_and_float():
    """float was missing from PAnd requires."""
    assert (0.0 and "x") == 0.0
    assert (1.5 and "x") == "x"

def test_and_str():
    assert ("" and 1) == ""
    assert ("hi" and 1) == 1

def test_and_list():
    """list was missing from PAnd requires."""
    assert ([] and 1) == []
    assert ([1] and 2) == 2

def test_and_dict():
    """dict was missing from PAnd requires."""
    assert ({} and 1) == {}
    assert ({"a": 1} and 2) == 2


# ---------------------------------------------------------------------------
# 4. or — short-circuit: returns first truthy operand, or last operand
# ---------------------------------------------------------------------------

def test_or_bool():
    assert (True or False) == True
    assert (False or True) == True
    assert (False or False) == False

def test_or_none():
    assert (None or 42) == 42
    assert (None or False) == False

def test_or_int():
    assert (0 or "hello") == "hello"
    assert (1 or "hello") == 1

def test_or_float():
    """float was missing from POr requires."""
    assert (0.0 or "x") == "x"
    assert (1.5 or "x") == 1.5

def test_or_str():
    assert ("" or 1) == 1
    assert ("hi" or 1) == "hi"

def test_or_list():
    """list was missing from POr requires."""
    assert ([] or 1) == 1
    assert ([1] or 2) == [1]

def test_or_dict():
    """dict was missing from POr requires."""
    assert ({} or 1) == 1
    assert ({"a": 1} or 2) == {"a": 1}


# ---------------------------------------------------------------------------
# Run all tests
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import sys
    failed = 0
    for name, obj in list(globals().items()):
        if name.startswith("test_") and callable(obj):
            try:
                obj()
            except AssertionError as e:
                print(f"FAIL: {name} — {e}", file=sys.stderr)
                failed += 1
    if failed:
        print(f"\n{failed} test(s) failed", file=sys.stderr)
        sys.exit(1)
    else:
        print("All tests passed")
