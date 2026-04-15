program Core;
procedure not_b(x : bool) returns (r : bool) {
  r := !x;
};
procedure and_b(x : bool, y : bool) returns (r : bool) {
  if (x) {
    r := y;
  } else {
    r := false;
  }
};
procedure or_b(x : bool, y : bool) returns (r : bool) {
  if (x) {
    r := true;
  } else {
    r := y;
  }
};
procedure xor_b(x : bool, y : bool) returns (r : bool) {
  var ny : bool;
  var t1 : bool;
  var nx : bool;
  var t2 : bool;
  call ny := not_b(y);
  call t1 := and_b(x, ny);
  call nx := not_b(x);
  call t2 := and_b(nx, y);
  call r := or_b(t1, t2);
};
procedure test_xor(a : bool, b : bool) returns (c : bool) {
  call c := xor_b(a, b);
};
