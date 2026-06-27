# Native @snapshot pre-state capture decorator (capture is a parameter).
@snapshot(lambda x: x, name="v0")
def f(x: int) -> int:
    ...
