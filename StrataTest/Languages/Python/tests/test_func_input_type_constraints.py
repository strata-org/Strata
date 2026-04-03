from typing import Union

def Mul(x: int | bool, y: int | bool = True) -> int:
    return x * y 

def Sum(x: Union[int , bool], y: Union[int , bool] = None) -> int | bool:
    if y == None:
      return x
    return x + y 

def List_Dict_index(l: List[Dict[str, Any]], i: int,  s: str) -> int:
    return l[i][s]


a = Mul(1, True)
a = Sum(1, None)
a = List_Dict_index([{ "a": 1 }, {"b": 2}], 0, "a")
