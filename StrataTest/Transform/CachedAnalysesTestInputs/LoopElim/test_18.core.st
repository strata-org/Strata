program Core;

const N : int;
axiom [ax_N]: (N >= 0);

procedure constBoundLoop() returns (r : int)
{
  var i : int;
  r := 0;
  i := 0;
  while (i < N)
    invariant ((0 <= i) && (i <= N))
    invariant (r >= 0)
  {
    r := r + i;
    i := i + 1;
  }
};
