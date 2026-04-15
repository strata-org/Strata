program Core;
procedure and_op(x : bool, y : bool) returns (r : bool) {
  if (x) {
    r := y;
  } else {
    r := false;
  }
};
procedure test_and(a : bool, b : bool) returns (c : bool) {
  call c := and_op(a, b);
};
