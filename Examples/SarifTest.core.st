program Core;

// Simple test program for SARIF output
procedure AddPositive(x : int, y : int) returns (z : int)
spec {
  requires [x_positive]: (x > 0);
  requires [y_positive]: (y > 0);
  ensures [result_positive]: (z > 0);
  ensures [result_sum]: (z == x + y);
}
{
  z := x + y;
};
