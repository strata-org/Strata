program Core;

const N : int;
axiom [ax_N]: (0 <= N);

procedure TwoLoops() returns ()
{
  var i : int;
  var j : int;

  i := 0;
  while (i < N)
  invariant ((0 <= i) && (i <= N))
  {
      i := (i + 1);
  }

  j := 0;
  while (j < N)
  invariant ((0 <= j) && (j <= N))
  {
      j := (j + 1);
  }
  
};
