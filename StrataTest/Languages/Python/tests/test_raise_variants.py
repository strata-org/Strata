# Test: raise statement in various positions
# Note: Functions that always raise and never return (raise_bare_in_except,
# raise_new_in_except, raise_at_top_level) produce "unknown" for the return
# type constraint because there is no feasible return path, making the
# postcondition unprovable.

def raise_in_try() -> str:
    result: str = ""
    try:
        raise Exception("err")
        result = "unreachable"
    except Exception:
        result = "caught"
    assert result == "caught", "handler should catch raise in try"
    return result

def raise_bare_in_except() -> str:
    try:
        raise Exception("original")
    except Exception:
        raise

def raise_new_in_except() -> str:
    try:
        raise Exception("original")
    except Exception:
        raise Exception("replaced")

def raise_at_top_level() -> str:
    raise Exception("top level")

raise_in_try()
raise_bare_in_except()
raise_new_in_except()
raise_at_top_level()
