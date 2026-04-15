program Core;

procedure subtractLoop(a : int, b : int) returns (diff : int)
{
  diff := a;
  var i : int;
  i := 0;
  while (i < b)
  {
    diff := diff - 1;
    i := i + 1;
  }
};
