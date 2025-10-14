int simpleTest(int x)
  __CPROVER_requires((x > 0) && (x < 10))
  __CPROVER_ensures(1)
{
  __CPROVER_assume(x > 0);
  __CPROVER_assume(x < 10);
  int sum = 0;
  int count = 0;
  while(count < 5) {
    count++;
    sum += x;
  }
  __CPROVER_assert(sum > 0, "sum_pos");
  return sum;
}