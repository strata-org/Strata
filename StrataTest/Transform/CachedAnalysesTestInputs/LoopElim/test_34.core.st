program Core;

const M : int;
axiom [ax_M]: (M >= 0);

procedure fillForward() returns (r : int)
{
  var i : int;
  r := 0;
  i := 0;
  while (i < M)
    invariant ((0 <= i) && (i <= M))
  {
    r := r + 1;
    i := i + 1;
  }
};

procedure fillBackward() returns (r : int)
{
  var i : int;
  r := 0;
  i := M;
  while (i > 0)
    invariant ((0 <= i) && (i <= M))
  {
    r := r + 1;
    i := i - 1;
  }
};
