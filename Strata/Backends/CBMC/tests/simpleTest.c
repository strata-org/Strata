int simpleTest(int x, int y)
  __CPROVER_requires(y > 0)
  __CPROVER_ensures(1)
{
  int z;
  __CPROVER_assume(y > 0);
  __CPROVER_assume(x > 0);
  __CPROVER_assume(y < 90);
  __CPROVER_assume(x < 90);
  z = x + y;
  __CPROVER_assert(z > x, "test_assert");
  if(z > 10) {
    z = z - 1;
  } else {
    z = z + 1;
  }
  return 0;
}