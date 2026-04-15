program Core;
procedure abs(x : int) returns (r : int) {
  if (x < 0) {
    r := 0 - x;
  } else {
    r := x;
  }
};
procedure dist(a : int, b : int) returns (d : int) {
  var diff : int;
  diff := a - b;
  call d := abs(diff);
};
procedure measure(p : int, q : int) returns (m : int) {
  call m := dist(p, q);
};
