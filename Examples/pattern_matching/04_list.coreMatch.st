program CoreMatch;

// Monomorphic List of int: natural-style recursion on `tl`.

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function length(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => 1 + length(tl);
  }
};

rec function sum(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => hd + sum(tl);
  }
};

rec function allPositive(xs : List) : bool
{
  match xs {
    arm Nil() => true;
    arm Cons(hd : int, tl : List) => hd > 0 && allPositive(tl);
  }
};

rec function containsZero(xs : List) : bool
{
  match xs {
    arm Nil() => false;
    arm Cons(hd : int, tl : List) => hd == 0 || containsZero(tl);
  }
};
