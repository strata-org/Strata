program Boogie;

procedure simpleTest (x: int, y: int) returns (ret : int)
spec {
}
{
  assume [assume_pos]: (x > 0);
  assume [assume_smol]: (x < 10);
  var sum : int;
  sum := 0;
  var count : int;
  count := 0;
  while
  (count < x)
  invariant (sum == count * x);
  {
    count := count + 1;
    sum := sum + x;
  }
  assert [assert_pos]: (sum > 0);
  ret := sum;
};