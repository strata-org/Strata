# Test: soundness of multiple except handler dispatch
# Verifies that the analysis does NOT assume a specific handler catches.
# Since we don't model exception types, each handler is a possible match.

class ErrorA(Exception):
    pass
class ErrorB(Exception):
    pass

def only_first_handler_matches() -> str:
    result: str = ""
    try:
        raise ErrorA("a]")
        result = "unreachable"
    except ErrorA:
        result = "caught_a"
    except ErrorB:
        result = "caught_b"
    # In Python, only the ErrorA handler runs, so result == "caught_a".
    # But since we over-approximate, the analysis must consider both handlers.
    # Therefore this assert should be UNKNOWN (not pass), because on the path
    # where ErrorB handler fires, result == "caught_b" != "caught_a".
    assert result == "caught_a", "only ErrorA handler should match"
    return result

only_first_handler_matches()
