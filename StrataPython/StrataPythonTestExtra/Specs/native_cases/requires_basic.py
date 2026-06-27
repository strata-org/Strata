# Native @requires precondition decorator.
@requires(lambda x: x >= 0)
def f(x: int) -> int:
    ...
