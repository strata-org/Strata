# Native @modifies frame decorator (target is a parameter).
@modifies(lambda x: x)
def f(x: int) -> int:
    ...
