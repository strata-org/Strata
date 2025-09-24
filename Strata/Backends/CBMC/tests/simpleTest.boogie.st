program Boogie;

procedure simpleTest(x : int, y : int) returns (ret : int)
spec {
  //requires [x_positive]:    (x > 0);
}
{
  var z : int;
  z := x;
  //assume [foo]: z < 10;
  z := z + 1;
  ret := 0;
};
