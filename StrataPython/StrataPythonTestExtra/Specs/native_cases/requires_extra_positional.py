# Extra positional argument after the lambda: warned, but the predicate is still
# recognized.
@requires(lambda x: x >= 0, "extra")
def f(x: int) -> int:
    ...
