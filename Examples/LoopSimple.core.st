program Core;

procedure loopSimple (n: int, out r: int)
spec {
  requires (int.ge(n, 0));
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(int.lt(i, n))
    decreases int.sub(n, i)
    invariant int.le(i, n)    
    invariant (int.div(int.mul(i, int.sub(i, 1)), 2) == sum)
  {
    sum := int.add(sum, i);
    i := int.add(i, 1);
  }
  assert [sum_assert]: (int.div(int.mul(n, int.sub(n, 1)), 2) == sum);
  assert [neg_cond]: (i == n);
  r := sum;
};
