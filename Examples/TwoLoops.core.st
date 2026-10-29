program Core;

const N : int;
axiom [ax_N]: int.le(0, N);

procedure TwoLoops()
{
  var i : int;
  var j : int;

  i := 0;
  while (int.lt(i, N))
  invariant (int.le(0, i) && int.le(i, N))
  {
      i := int.add(i, 1);
  }

  j := 0;
  while (int.lt(j, N))
  invariant (int.le(0, j) && int.le(j, N))
  {
      j := int.add(j, 1);
  }
  
};
