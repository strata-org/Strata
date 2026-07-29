program Core;

// Two independent uninterpreted functions, each with their own axioms.
// removeIrrelevantAxioms --functions f should prune g's axioms (and vice versa).

function f(x: int): int;
axiom [f_positive]: forall x : int :: int.gt(f(x), 0);
axiom [f_monotone]: forall x : int , y : int :: int.lt(x, y) ==> int.lt(f(x), f(y));

function g(x: int): int;
axiom [g_negative]: forall x : int :: int.lt(g(x), 0);
axiom [g_idempotent]: forall x: int :: g(g(x)) == g(x);

// h calls f, so h's axiom is also relevant when focusing on f.
function h(x: int): int;
axiom [h_def]: forall x : int :: h(x) == int.add(f(x), 1);

procedure TestF(x: int, out result: int)
spec {
  ensures [result_positive]: int.gt(result, 0);
}
{
  result := f(x);
};
