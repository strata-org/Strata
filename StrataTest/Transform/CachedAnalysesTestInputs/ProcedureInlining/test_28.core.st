program Core;
procedure is_positive(x : int) returns (r : bool) {
  if (x > 0) {
    r := true;
  } else {
    r := false;
  }
};
procedure sign(x : int) returns (s : int) {
  var pos : bool;
  call pos := is_positive(x);
  if (pos) {
    s := 1;
  } else {
    if (x == 0) {
      s := 0;
    } else {
      s := 0 - 1;
    }
  }
};
procedure classify(a : int) returns (c : int) {
  call c := sign(a);
};
procedure run(n : int) returns (r : int) {
  call r := classify(n);
};
