# strata-args: --check-mode bugFinding --check-level full
class MyClass:
    def __init__(self, n: int):
        self.val : int = n

xs: list[int] = []
xs.append(1)
if xs:
    x: int = xs[0]

ys: list[int] = []
xs.unknown_method_that_may_modify_arguments(ys)
if ys:
    y: int = ys[0]
