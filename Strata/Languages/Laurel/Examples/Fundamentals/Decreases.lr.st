procedure A(x: nat)
  decreases x, 1
{
  B(x);
}

procedure B(x: nat)
  decreases x, 0
{
  if x != 0 { A(x-1); }
}
