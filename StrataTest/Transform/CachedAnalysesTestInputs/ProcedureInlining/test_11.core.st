program Core;
procedure base(x : int, y : int) returns (r : int) {
  r := x + y;
};
procedure relay(a : int, b : int) returns (c : int) {
  call c := base(a, b);
};
procedure entry(p : int, q : int) returns (s : int) {
  call s := relay(p, q);
};
