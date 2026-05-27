program Core;

function f (x : int) : int;
axiom [f_positive]: forall x : int :: f(x) > 0;
axiom [f_monotone]: forall x : int :: forall y : int :: x < y ==> f(x) < f(y);
function g (x : int) : int;
function h (x : int) : int;
axiom [h_def]: forall x : int :: h(x) == f(x) + 1;
procedure TestF (x : int, out result : int)
spec {
  ensures [result_positive]: result > 0;
  } {
  result := f(x);
};
