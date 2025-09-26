program C_Simp;

int procedure simpleTest (x: int, y: int)
  //@pre y > 0;
  //@post true;
{
  var z : int;
  //@assume [test_assume_y_pos] y > 0;
  //@assume [test_assume_x_pos] x > 0;
  //@assume [test_assume_y_smol] y < 90;
  //@assume [test_assume_x_smol] x < 90;
  z = x + y;
  //@assert [test_assert] z > x;
  if (z > 10) {
    z = z - 1;
  } else {
    z = z + 1;
  }
  return 0;
}
