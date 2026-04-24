program Core;

// Two independent uninterpreted functions, each with their own axioms.
// removeIrrelevantAxioms --functions f should prune g's axioms (and vice versa).

function f(x: int): int;
axiom [f_positive]: forall x: int :: f(x) > 0;
axiom [f_monotone]: forall x: int, y: int :: x < y ==> f(x) < f(y);

function g(x: int): int;
axiom [g_negative]: forall x: int :: g(x) < 0;
axiom [g_idempotent]: forall x: int :: g(g(x)) == g(x);

// h calls f, so h's axiom is also relevant when focusing on f.
function h(x: int): int;
axiom [h_def]: forall x: int :: h(x) == f(x) + 1;

procedure TestF(x: int, out result: int)
spec {
  ensures [result_positive]: result > 0;
}
{
  result := f(x);
};
