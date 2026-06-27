# Native @ensures postcondition decorator (with the `result` binder).
@ensures(lambda result: result >= 0)
def f(x: int) -> int:
    ...
