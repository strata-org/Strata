program Core;

procedure safe_bv_ops (x : bv32, y : bv32, out r : bv32)
{
  var a : bv32;
  var b : bv32;
  var c : bv32;
  var d : bv32;
  var e : bv32;
  var f : bv32;
  a := x safe+ y;
  b := x safe- y;
  c := x safe* y;
  d := safe_neg x;
  e := x safesdiv y;
  f := x safesmod y;
  r := a;
};
