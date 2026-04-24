program Core;

procedure add(x : int, y : int, out r : int)
spec {
  requires (x >= 0);
  requires (y >= 0);
  ensures (r >= 0);
} {
  r := x + y;
};
