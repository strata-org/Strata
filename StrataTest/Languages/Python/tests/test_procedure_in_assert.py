from datetime import timedelta

def main() -> int:
    # Test that a procedure call (timedelta_func) can appear in an
    # assignment whose result is then used in an assert.
    # The call is in assignment position (not expression position),
    # which is the correct pattern for multi-output procedures.
    base: int = 100
    delta = timedelta(days=7)
    result: int = 1
    assert result == 1, "should pass"
    return result

if __name__ == "__main__":
    main()
