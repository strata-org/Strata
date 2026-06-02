# strata-args: --typed-python --check-mode bugFinding --check-level full
# Variables declared inside if/while blocks. Strata's hoisting pass
# pulls all locals to the top of the procedure; verify it works
# correctly with typed locals across control-flow scopes.
def conditional_decl(x: int) -> int:
    assert x >= 0
    if x > 10:
        y: int = x * 2
        return y
    z: int = x + 1
    return z


def shadowed_locals(x: int, y: int) -> int:
    assert x >= 0
    assert y >= 0
    if x > y:
        result: int = x - y
    else:
        result: int = y - x
    return result


def loop_local(n: int) -> int:
    assert n >= 0
    assert n <= 50
    sum: int = 0
    i: int = 0
    while i < n:
        delta: int = i * 2
        sum = sum + delta
        i = i + 1
    return sum
