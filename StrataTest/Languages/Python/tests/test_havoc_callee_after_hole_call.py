class MyClass:
    def __init__(self, n: int):
        self.val : int = n

xs = [1, 2]
xs.some_unmodeled_call_1(3)
assert xs == [1, 2], "expected unknown because xs should be havocked"


xs = [1,2]
ys = xs.some_unmodeled_call_2()
assert xs == [1, 2], "expected unknown because xs should be havocked" 


xs = [1,2]
xs.some_unmodeled_call_3.some_unmodeled_call_4()
assert xs == [1, 2], "expected unknown because xs should be havocked" 

xs = [1,2]
some_function().some_unmodeled_call_5()
assert xs == [1, 2], "expected pass nothing should be havocked" 

a : MyClass = MyClass(2)
a.val = 1
some_unmodeled_call_6(a)
assert a.val == 1, "expected unknown because heap should be havocked" 
