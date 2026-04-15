program Core;

procedure power(base : int, exp : int) returns (result : int)
{
  var i : int;
  result := 1;
  i := 0;
  while (i < exp)
  {
    result := result * base;
    i := i + 1;
  }
};
