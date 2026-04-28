# strata-args: --check-mode bugFinding --check-level full
class MyClass:
    def __init__(self, n: int):
        self.val : int = n

xs: list[int] = [1, 2]
xs.some_unmodeled_call_1(3)
assert xs == [1, 2], "expected unknown because xs should be havocked"

xs = [1,2]
ys: list[int] = xs.some_unmodeled_call_2()
assert xs == [1, 2], "expected unknown because xs should be havocked"

xs = [1,2]
xs.some_unmodeled_call_3.some_unmodeled_call_4()
assert xs == [1, 2], "chained call: receiver not havocked (chained attribute is not a Name)"

xs = [1,2]
some_function().some_unmodeled_call_5()
assert xs == [1, 2], "unrelated variable: nothing should be havocked"

a : MyClass = MyClass(2)
a.val = 1
some_unmodeled_call_6(a)
assert a.val == 1, "composite arg: heap not havocked (out of scope)"

xs2: list[int] = [1, 2]
ys2: list[int] = []
xs2.unknown_method_that_may_modify_arguments(ys2)
assert ys2 == [], "expected unknown because argument locals should be havocked"
