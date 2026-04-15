program Core;
procedure to_bool(x : int) returns (r : bool) {
  if (x == 0) {
    r := false;
  } else {
    r := true;
  }
};
procedure to_int(b : bool) returns (r : int) {
  if (b) {
    r := 1;
  } else {
    r := 0;
  }
};
procedure round_trip(x : int) returns (r : int) {
  var b : bool;
  call b := to_bool(x);
  call r := to_int(b);
};
procedure test(n : int) returns (m : int) {
  call m := round_trip(n);
};
