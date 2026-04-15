program Core;

procedure boolGuardLoop(flag : bool) returns (count : int)
{
  var done : bool;
  var i : int;
  count := 0;
  done := flag;
  i := 0;
  while (!done)
  {
    count := count + 1;
    i := i + 1;
    if (i >= 10) {
      done := true;
    }
  }
};
