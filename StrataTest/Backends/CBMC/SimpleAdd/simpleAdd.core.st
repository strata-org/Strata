program Core;
procedure simpleAdd (x : bv W32, y : bv W32) {

  assume (bv32.uLt(x, bv{32}(0xFFFF0000)));
  assume (bv32.uLt(y, bv{32}(0x00001111)));

  var z : bv W32 := bv{32}(0);
  z := bv32.add(x, y);

  assert [z_assertion]: (bv32.uLt(z, bv{32}(0xFFFF1110)));

};
