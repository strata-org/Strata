program Core;

procedure multiplyByAdd(a : int, b : int) returns (result : int)
{
  var i : int;
  result := 0;
  i := 0;
  while (i < b)
  {
    result := result + a;
    i := i + 1;
  }
};
