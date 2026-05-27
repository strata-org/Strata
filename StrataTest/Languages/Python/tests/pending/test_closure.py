def make_adder(n: int):
    def adder(x: int) -> int:
        return x + n
    return adder

def test():
    add5 = make_adder(5)
    assert add5(3) == 8, "closure"
test()
