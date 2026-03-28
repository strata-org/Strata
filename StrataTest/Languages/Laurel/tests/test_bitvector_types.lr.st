// Bitvector types through the GOTO/CBMC pipeline.

procedure identity32(x: bv32) returns (r: bv32) {
  r := x
};

procedure identity8(x: bv8) returns (r: bv8) {
  r := x
};

procedure localBv() returns (r: bv16) {
  var x: bv16 := r;
  r := x
};
