# Malformed @requires: the argument is not a lambda. Must be a hard error.
@requires(42)
def f(x: int) -> int:
    ...
