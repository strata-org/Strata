# strata-args: --check-mode bugFinding --check-level full
def test_bug_finding_unreachable(x: int) -> None:
    assert x != x, "impossible condition"
    if x > 0:
        if x < 0:
            assert False, "dead code"
