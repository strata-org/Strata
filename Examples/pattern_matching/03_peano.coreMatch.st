program CoreMatch;

// Peano naturals: natural-style recursion on the `pred` field.

datatype Nat () { Zero(), Succ(pred : Nat) };

rec function toInt(n : Nat) : int
{
  match n {
    arm Zero()           => 0;
    arm Succ(pred : Nat) => 1 + toInt(pred);
  }
};

rec function isZero(n : Nat) : bool
{
  match n {
    arm Zero()           => true;
    arm Succ(pred : Nat) => false;
  }
};

rec function double(n : Nat) : Nat
{
  match n {
    arm Zero()           => Zero();
    arm Succ(pred : Nat) => Succ(Succ(double(pred)));
  }
};
