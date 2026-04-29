"""
Edge-case tests for Python truthiness semantics (passing cases).

Tests that the Strata runtime (PNot, PAnd, POr) correctly models
Python's truthiness for the types identified in issue #934.

Non-passing cases are in tests/pending/test_truthiness_bool_eq.py,
test_truthiness_not_eq.py, and test_truthiness_float_and_or.py.
"""


# ---------------------------------------------------------------------------
# not — fully verified types
# ---------------------------------------------------------------------------

def test_not_none():
    assert (not None) == True

def test_not_bool():
    assert (not True) == False
    assert (not False) == True


# ---------------------------------------------------------------------------
# and — short-circuit: returns first falsy operand, or last operand
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

def test_and_str():
    assert ("" and 1) == ""
    assert ("hi" and 1) == 1

def test_and_list():
    assert ([] and 1) == []
    assert ([1] and 2) == 2

def test_and_dict():
    assert ({} and 1) == {}
    assert ({"a": 1} and 2) == 2


# ---------------------------------------------------------------------------
# or — short-circuit: returns first truthy operand, or last operand
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

def test_or_str():
    assert ("" or 1) == 1
    assert ("hi" or 1) == "hi"

def test_or_list():
    assert ([] or 1) == 1
    assert ([1] or 2) == [1]

def test_or_dict():
    assert ({} or 1) == 1
    assert ({"a": 1} or 2) == {"a": 1}


# ---------------------------------------------------------------------------
# Run all tests
# ---------------------------------------------------------------------------

test_not_none()
test_not_bool()
test_and_bool()
test_and_none()
test_and_int()
test_and_str()
test_and_list()
test_and_dict()
test_or_bool()
test_or_none()
test_or_int()
test_or_str()
test_or_list()
test_or_dict()
