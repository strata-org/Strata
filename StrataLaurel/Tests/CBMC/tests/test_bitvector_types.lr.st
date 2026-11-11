// Bitvector types through the GOTO/CBMC pipeline.

procedure identity32(x: bv 32) returns (r: bv 32)
  opaque
{
  r := x
};

procedure identity8(x: bv 8) returns (r: bv 8)
  opaque
{
  r := x
};

procedure localBv() returns (r: bv 16)
  opaque
{
  var x: bv 16 := r;
  r := x
};

procedure main()
  opaque
{
  var a: bv 32 := identity32($intToBv32(7));
  assert a == $intToBv32(7);
  var b: bv 8 := identity8($intToBv8(255));
  assert b == $intToBv8(255);
  var c: bv 16 := localBv();
  assert c == c;
  assert a == $intToBv32(8)
};
