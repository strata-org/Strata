// Regression test for #1331: old(h) where h is read-only (not in modifies).
// BoogieToStrata must widen the effective-modifies set so h is emitted `inout`
// and the `old h` fvar resolves in Strata's typechecker. Pre-fix this produced
// `Cannot find this fvar in the context! old h`.
var g: int;
var h: int;
procedure p() returns ();
  modifies g;
  free ensures g == old(h);
implementation p() { g := h; return; }
