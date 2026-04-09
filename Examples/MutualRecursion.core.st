program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function isEven (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then true else isOdd(MyNat..pred(n))
}
function isOdd (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then false else isEven(MyNat..pred(n))
};

procedure isEvenOddTest() returns ()
{
  assert [zeroEven]: isEven(Zero()) == true;
  assert [zeroNotOdd]: isOdd(Zero()) == false;
  assert [oneOdd]: isOdd(Succ(Zero())) == true;
  assert [oneNotEven]: isEven(Succ(Zero())) == false;
};