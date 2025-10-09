program Boogie;

procedure simpleTest (x: int, y: int) returns (ret : int)
spec {
  requires [x_pos]: (x > 0);
  requires [x_smol]: (x < 10);
}
{
  assume [assume_pos]: (x > 0);
  assume [assume_smol]: (x < 10);
  var sum : int;
  sum := 0;
  var count : int;
  count := 0;
  while
  (count < 5)
  {
    count := count + 1;
    sum := sum + x;
  }
  assert [assert_pos]: (sum > 0);
  ret := sum;
};