# Native @ghost with a declared type= and init= initializer.
@ghost(name="g", type=int, init=0)
def f(x: int) -> int:
    ...
