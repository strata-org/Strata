// {:smack}
// Regression test for InferModifies = true.
//
// This procedure mutates the global variable `g` but has NO explicit
// `modifies g;` clause.  With InferModifies = true, Boogie's
// ModSetCollector should infer the modifies clause so that the
// BoogieToStrata translator emits `inout g` for procedure p.
// If InferModifies is ever disabled or broken, this file will fail
// to translate correctly (g would be treated as read-only instead
// of inout).

var g: int;

procedure p()
{
  g := 1;
}
