program Core;

function f (x : int) : int;
axiom [f_positive]: forall __q0 : int :: f(__q0) > 0;
axiom [f_monotone]: forall __q0 : int :: forall __q1 : int :: __q0 < __q1 ==> f(__q0) < f(__q1);
function g (x : int) : int;
function h (x : int) : int;
axiom [h_def]: forall __q0 : int :: h(__q0) == f(__q0) + 1;
procedure TestF (x : int, out result : int)
spec {
  ensures [result_positive]: result > 0;
  } {
  result := f(x);
};
