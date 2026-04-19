// Bitvector types through the GOTO/CBMC pipeline.

procedure identity32(x: bv 32) returns (r: bv 32) {
  r := x
};

procedure identity8(x: bv 8) returns (r: bv 8) {
  r := x
};

procedure localBv() returns (r: bv 16) {
  var x: bv 16 := r;
  r := x
};
