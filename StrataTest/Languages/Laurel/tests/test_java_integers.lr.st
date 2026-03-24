constrained jbyte = x: int where x >= -128 && x <= 127 witness 0
constrained jint  = x: int where x >= -2147483648 && x <= 2147483647 witness 0
constrained jchar = x: int where x >= 0 && x <= 65535 witness 0

procedure byteInRange(b: jbyte) {
  assert b >= -128;
  assert b <= 127
};

procedure intInRange(n: jint) {
  assert n >= -2147483648;
  assert n <= 2147483647
};

procedure charIsUnsigned(c: jchar) {
  assert c >= 0
};

procedure safeByteAdd(a: jbyte, b: jbyte) returns (r: jint) {
  r := a + b;
  assert r >= -256;
  assert r <= 254
};

procedure byteToInt(b: jbyte) returns (r: jint) {
  r := b
};
