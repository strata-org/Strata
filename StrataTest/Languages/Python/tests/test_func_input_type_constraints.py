def Mul(x: int | bool, y: int | bool = "abc") -> int:
    return x * y 

def Sum(x: Union[int , bool], y: Union[int , bool] = None) -> int:
    if y == None:
      return x
    return x + y 

a = Mul(1, True)
a = Sum(1, None)
