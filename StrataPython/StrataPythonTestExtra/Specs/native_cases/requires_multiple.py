# Multiple @requires accumulate into multiple preconditions.
@requires(lambda x: x >= 0)
@requires(lambda x: x <= 100)
def f(x: int) -> int:
    ...
