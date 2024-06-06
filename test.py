from typing import Literal, Tuple

myEnum =  Tuple[Literal['1'], int] | Tuple[Literal['2'], str]

def f(x : myEnum) -> int: 
  match x:
    case ('1', i):
      print(i)
      return 4
    case ('2', s):
      print(s)
      return 2
    # case _:
    #   pass
    #   return 1  
  return 2
    

