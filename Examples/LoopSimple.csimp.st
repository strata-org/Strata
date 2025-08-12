program C_Simp;

int procedure loopSimple (n: int)
  //@pre (n >= 0);
  //@post true;
{
  var sum : int;
  var i : int;

  sum = 0;
  i = 0;
  while(i < n)
  //@decreases (n-i)
  //@invariant (i <= n && ((i * (i-1))/2 == sum))
  {
    sum = sum + i;
    i = i + 1;
  }
  //@assert [sum_assert] ((n * (n-1))/2 == sum);
  return sum;
}