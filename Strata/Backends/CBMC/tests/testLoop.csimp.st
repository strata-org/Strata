program C_Simp;

int procedure simpleTest (x: int, y: int)
  //@pre ((x > 0) && (x < 10));
  //@post true;
{
  //@assume [assume_pos] (x > 0);
  //@assume [assume_smol] (x < 10);
  var sum : int;
  sum = 0;
  var count : int;
  count = 0;
  while
  (count < x)
  //@decreases (x-count)
  //@invariant (count <= x && (sum == (count * x)))
  {
    count = count + 1;
    sum = sum + x;
  }
  //@assert [assert_pos] (sum > 0);
  return sum;
}