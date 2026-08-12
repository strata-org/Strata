program Core;

function f (x : int) : int;
axiom [f_positive]: forall x : int :: int.gt(f(x), 0);
axiom [f_monotone]: forall x : int :: forall y : int :: int.lt(x, y) ==> int.lt(f(x), f(y));
function g (x : int) : int;
function h (x : int) : int;
axiom [h_def]: forall x : int :: h(x) == int.add(f(x), 1);
procedure TestF (x : int, out result : int)
spec {
  ensures [result_positive]: int.gt(result, 0);
  } {
  result := f(x);
};
