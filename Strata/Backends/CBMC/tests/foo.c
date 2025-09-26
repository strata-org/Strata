int simpleTest(int x, int y)
  __CPROVER_requires(x > 0)
  __CPROVER_ensures(1)
{
  int z;
  z = x;
  //assume [foo]: z < 10;
  z = z + 1;
  return z;
}