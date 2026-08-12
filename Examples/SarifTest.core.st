program Core;

// Simple test program for SARIF output
procedure AddPositive(x : int, y : int, out z : int)
spec {
  requires [x_positive]: int.gt(x, 0);
  requires [y_positive]: int.gt(y, 0);
  ensures [result_positive]: int.gt(z, 0);
  ensures [result_sum]: (z == int.add(x, y));
}
{
  z := int.add(x, y);
};
