constrained i8  = x: int where x >= -128 && x <= 127 witness 0
constrained i32 = x: int where x >= -2147483648 && x <= 2147483647 witness 0
constrained u16 = x: int where x >= 0 && x <= 65535 witness 0

procedure i8InRange(b: i8) {
  assert b >= -128;
  assert b <= 127
};

procedure i32InRange(n: i32) {
  assert n >= -2147483648;
  assert n <= 2147483647
};

procedure u16IsUnsigned(c: u16) {
  assert c >= 0;
  assert c <= 65535
};

procedure safeI8Add(a: i8, b: i8) returns (r: i32) {
  r := a + b;
  assert r >= -256;
  assert r <= 254
};

procedure i8ToI32(b: i8) returns (r: i32) {
  r := b
};
