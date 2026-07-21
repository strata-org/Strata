program Core;

procedure safe_bv_ops (x : bv32, y : bv32, out r : bv32)
{
  var a : bv32;
  var b : bv32;
  var c : bv32;
  var d : bv32;
  var e : bv32;
  var f : bv32;
  a := Bv.SafeAdd(x, y);
  b := Bv.SafeSub(x, y);
  c := Bv.SafeMul(x, y);
  d := Bv.SafeNeg(x);
  e := Bv.SafeSDiv(x, y);
  f := Bv.SafeSMod(x, y);
  r := a;
};
