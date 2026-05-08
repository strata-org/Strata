program CoreMatch;

// Constructor calls in arm bodies plus natural-style recursion.

datatype List () { Nil(), Cons(hd : int, tl : List) };
datatype Pair () { MkPair(first : int, second : List) };

rec function map_inc(xs : List) : List
{
  match xs {
    arm Nil() => Nil();
    arm Cons(hd : int, tl : List) => Cons(hd + 1, map_inc(tl));
  }
};

rec function filter_pos(xs : List) : List
{
  match xs {
    arm Nil() => Nil();
    arm Cons(hd : int, tl : List) =>
      if hd > 0 then Cons(hd, filter_pos(tl)) else filter_pos(tl);
  }
};

function head_or_zero_with_rest(xs : List) : Pair
{
  match xs {
    arm Nil()                       => MkPair(0, Nil());
    arm Cons(hd : int, tl : List)   => MkPair(hd, tl);
  }
};
