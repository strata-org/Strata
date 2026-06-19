/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import StrataDDM.Util.IO
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.LaurelCompilationPipeline
meta import all StrataTest.Languages.Laurel.VerifyMetricsHarness

/-!
# Polymorphism corpus

The feature corpus for user-level polymorphism, driven by the shared `Case`/`checkCase`
harness (`VerifyMetricsHarness`). Each block is a `List Case` table + a `checkCases` runner,
with must-fail twins pinning soundness. Areas: a genuinely polymorphic function; polymorphic
procedures (freshening + monomorphization + witness); generic composites (monomorphization,
nested generics, `new C<τ>`, chained writes); generic datatypes (native Core parametric
datatypes); generic composite methods, inheritance, upcasting, and field-type concretization.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-! ## End-to-end: a genuinely polymorphic function

The first program that exercises the full tyvar substrate: a polymorphic
`function id<T>(x: T): T` declared with a `<T>` binder (grammar), `T` resolved
to `.TVar` in scope (resolution), lowered to a Core `ftvar` and instantiated by
Core's HM at the `id(5)` call site (translation + Core). If this verifies, the
substrate works end-to-end — not just compiles. -/
def polyIdProgram := r"
function id<T>(x: T): T
{
    x
};

procedure useIt()
  opaque
{
    var a: int := id(5);
    assert a == 5
};"

def runPolyIdTest : IO Unit := do
  let m ← corpusMetricsOf "poly_id" polyIdProgram
  IO.println (serializeMetrics "poly_id" m)
  unless m.translated do
    throw (IO.userError "poly_id: a polymorphic function failed to translate to Core")
  unless m.numFailures == 0 do
    throw (IO.userError s!"poly_id: expected all-verified, got numFailures={m.numFailures}")

#guard_msgs (drop info, error) in
#eval runPolyIdTest

/-! ## Polymorphic procedures verify soundly (CallElim per-call-site freshening)

Polymorphic *procedures* are now SUPPORTED. They route through TransparencyPass →
`$asFunction` + CallElim contract-inlining; CallElim renames the callee's type
variables to globally-fresh names at each call site (`freshenTypeArgsSubst`), so
the same procedure can be instantiated at different concrete types in one body.

This SUPERSEDES the earlier `runUnsupportedGates` gate, which was based on a wrong
premise: the gate's comment claimed poly procedures "silently mis-verify" via a
`ProcedureType` separate-instantiation bug. Empirically that path is never taken —
procedures are eliminated by CallElim *before* Core's `.call`/`ProcedureType` type
check runs. The real (and only) failure was multi-instantiation in one body, which
was a LOUD type error ("Impossible to unify T with bool") that ABORTED whole-program
type checking and masked unrelated obligations. These tests pin the fix:
single-instantiation is sound, multi-instantiation works, and a poison
multi-instantiation no longer masks a sibling procedure's real bug. -/

/-- Identity procedure with `ensures y == x`, instantiated at int. The true
    assertion must verify; the false one must fail (soundness). -/
def polyProcSound := r"
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };
procedure useGood() opaque { var a: int := idp(5); assert a == 5 };
procedure useBad() opaque { var b: int := idp(5); assert b == 6 };"

/-- Same procedure instantiated at TWO different types in ONE body — the case that
    previously aborted with "Impossible to unify T with bool". Must verify. -/
def polyProcMultiInst := r"
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };
procedure useTwo() opaque {
    var a: int := idp(5);
    assert a == 5;
    var b: bool := idp(true);
    assert b == true
};"

/-- A poison multi-instantiation in one procedure must NOT abort the whole program
    and mask a real bug (`assert 1 == 2`) in a sibling procedure. Regression for
    the abort-masking ship-blocker. -/
def polyProcNoAbortMask := r"
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };
procedure realBug() opaque { assert 1 == 2 };
procedure poison() opaque {
    var a: int := idp(5);
    assert a == 5;
    var b: bool := idp(true);
    assert b == true
};"

/-- SOUNDNESS, not just typeability: under multi-instantiation the freshened
    postcondition must still be a usable fact AND a false assertion must still
    fail. Here the false `assert c == 99` is the THIRD instantiation — pins that
    the per-site freshening doesn't drift across many sites and doesn't make any
    site's assume vacuous (which would wrongly let the false assert pass). -/
def polyProcFalseAmongMany := r"
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };
procedure m() opaque {
    var a: int := idp(5);
    var b: bool := idp(true);
    var c: int := idp(9);
    assert a == 5;
    assert b == true;
    assert c == 99
};"

/-- SOUNDNESS: a freshened PRECONDITION must still gate. `pos` requires `x > 0`;
    called with `-3` at one of two differently-typed sites, the precondition
    violation must be reported (not erased by the type-var freshening). -/
def polyProcPrecondGated := r"
procedure pos<T>(x: int, t: T) returns (y: T) requires x > 0 opaque ensures y == t { y := t };
procedure m() opaque {
    var a: int := pos(5, 1);
    var b: bool := pos(-3, true);
    assert true
};"

private def outerInner := "composite Box<T> { var val: T }\nprocedure inner<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };\nprocedure outer<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := inner(b) };\n"

-- Polymorphic procedures ride per-call-site type-var FRESHENING (CallElim) for value-`T`,
-- and per-instantiation MONOMORPHIZATION when a generic composite is materialized at a type
-- var (in the signature OR body). Uncalled composite-`T` procs are checked at a synthetic
-- non-singleton WITNESS. The big risks pinned here: multi-inst must not abort-mask siblings;
-- freshening must couple input/output slots (no cross-slot drift) and keep pre/postconditions
-- non-vacuous; divergent chains must fail loud (depth cap); the hybrid partition must hold
-- (pure value-`T` stays on freshening). The `tc_*` cases pin that #1121's gradual checker is
-- NOT weakened by the `.TVar`-consistency arms — wrong programs still reject.
def polyProcedureCorpus : List Case := [
  { name := "poly_proc_sound", outcome := .failsExactly 1,
    why := "single inst: true verifies, the false `assert b == 6` fails (sound + complete)"
    src := polyProcSound },
  { name := "poly_proc_multi", outcome := .verifies,
    why := "multi-inst (idp(5)+idp(true) in one body) verifies — per-call-site freshening, no 'unify T with bool'"
    src := polyProcMultiInst },
  { name := "poly_proc_no_abort_mask", outcome := .failsExactly 1,
    why := "a poison multi-inst must NOT abort whole-program checking and mask realBug's `assert 1==2` (the ship-blocker)"
    src := polyProcNoAbortMask },
  { name := "poly_proc_false_among_many", outcome := .failsExactly 1,
    why := "false `assert c==99` on the 3rd inst still caught — freshening per-site postcondition non-vacuous, no drift"
    src := polyProcFalseAmongMany },
  { name := "poly_proc_precond_gated", outcome := .failsExactly 1,
    why := "a freshened precondition (`x>0` violated by pos(-3,..)) still gates a bad call"
    src := polyProcPrecondGated },
  -- CROSS-SLOT freshening: `callElimCmd` applies the same fresh subst to input types, output
  -- types, and pre/post EXPRESSIONS. `ensures r==x` COUPLES input+output type at each call —
  -- if a slot freshened to a different inst, the coupled obligation would be ill-formed or
  -- vacuous (silently unsound, invisible to the typechecker AND the sorry-stubbed CallElim
  -- proof). Verified at int+bool together, with a must-fail twin on EACH slot. This is the
  -- execution guardrail for the freshening, which has no live correctness proof.
  { name := "poly_proc_freshen_crossslot", outcome := .verifies,
    why := "`ensures r==x` coupling input+output type verifies at int AND bool (no cross-slot drift)"
    src := "procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };\nprocedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 7 && gb == true };" },
  { name := "poly_proc_freshen_crossslot_wrong_int", outcome := .failsExactly 1,
    why := "a wrong INT result must FAIL (one slot) — freshening soundness"
    src := "procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };\nprocedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 8 && gb == true };" },
  { name := "poly_proc_freshen_crossslot_wrong_bool", outcome := .failsExactly 1,
    why := "a wrong BOOL result must FAIL (the other slot) — freshening soundness"
    src := "procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };\nprocedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 7 && gb == false };" },
  -- Procedure monomorphization for a generic-composite param `f<T>(b: Box<T>)`: clone +
  -- substTypeVars per call-site inst, ids cleared so clones re-resolve independently. KEYSTONE
  -- is reading the boxed field `b#val` off the monomorph (param-passing alone passed for an
  -- adjacent reason without exercising field use).
  { name := "poly_proc_generic_composite_param", outcome := .verifies,
    why := "`unbox<T>(b: Box<T>)` reading `b#val` at int verifies (procedure monomorphization)"
    src := "composite Box<T> { var val: T }\nprocedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };\nprocedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := unbox(bx); assert got == 7 };" },
  { name := "poly_proc_generic_composite_param_wrong", outcome := .failsExactly 1,
    why := "reading `b#val`==7 then asserting got==8 must FAIL — the field read is real, not havoc'd"
    src := "composite Box<T> { var val: T }\nprocedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };\nprocedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := unbox(bx); assert got == 8 };" },
  -- multi-inst reading fields: `unbox` at int AND bool, each reading ITS monomorph's field
  -- (clone id-clearing is load-bearing; without it the bodies cross-link).
  { name := "poly_proc_generic_composite_param_multi", outcome := .verifies,
    why := "`unbox<T>` reading fields at int AND bool both verify (no clone cross-link)"
    src := "composite Box<T> { var val: T }\nprocedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };\nprocedure u() opaque { var bi: Box<int> := new Box<int>; bi#val := 7; var gi: int := unbox(bi); var bb: Box<bool> := new Box<bool>; bb#val := true; var gb: bool := unbox(bb); assert gi == 7 && gb == true };" },
  { name := "poly_proc_generic_composite_param_multi_wrong", outcome := .failsExactly 1,
    why := "a wrong bool read across int+bool monomorphs must FAIL (int passing must not mask bool)"
    src := "composite Box<T> { var val: T }\nprocedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };\nprocedure u() opaque { var bi: Box<int> := new Box<int>; bi#val := 7; var gi: int := unbox(bi); var bb: Box<bool> := new Box<bool>; bb#val := true; var gb: bool := unbox(bb); assert gi == 7 && gb == false };" },
  { name := "poly_proc_generic_composite_param_false_post", outcome := .failsExactly 1,
    why := "a FALSE postcondition on a Box<T>-param proc must FAIL — monomorphized contract is sound, not vacuous"
    src := "composite Box<T> { var val: T }\nprocedure pk<T>(b: Box<T>) returns (r: int) opaque ensures r == 0 { r := 1 };\nprocedure u() opaque { var bx: Box<int> := new Box<int>; var g: int := pk(bx); assert 1 == 1 };" },
  { name := "poly_proc_generic_composite_param_precond_wrong", outcome := .failsAtLeast 1,
    why := "a violated precondition on the generic field `b#val` must GATE — requires-clauses monomorphize + are checked"
    src := "composite Box<T> { var val: T }\nprocedure get7<T>(b: Box<T>) returns (r: T) requires b#val == 7 opaque ensures r == b#val { r := b#val };\nprocedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 5; var got: int := get7(bx); assert got == 7 };" },
  { name := "poly_proc_concrete_composite_param", outcome := .verifies,
    why := "a CONCRETE `Box<int>` param (no type vars) must still work"
    src := "composite Box<T> { var val: T }\nprocedure take(b: Box<int>) opaque { assert 1 == 1 };\nprocedure u() opaque { var x: Box<int> := new Box; assert 1 == 1 };" },
  -- #1121 coexistence — REJECT side. The `.TVar`-aware consistency arms (tvarize at
  -- registration; recursive `.Applied` arm; bare-name~instantiation arm) must NOT weaken the
  -- checker. Each of these is a type-incorrect program that must still be REJECTED; a leak
  -- here = the consistency relation was over-relaxed (and every accept-side test would stay green).
  { name := "tc_baseline_int_eq_true", outcome := .rejected,
    why := "#1121's non-poly checking untouched: `var x: int := true` rejects"
    src := "procedure u() opaque { var x: int := true; assert 1 == 1 };" },
  { name := "tc_baseline_cross_composite", outcome := .rejected,
    why := "`var x: Dog := new Cat` (cross-composite) rejects"
    src := "composite Dog { var a: int }\ncomposite Cat { var b: int }\nprocedure u() opaque { var x: Dog := new Cat; assert 1 == 1 };" },
  { name := "tc_boxint_to_boxbool", outcome := .rejected,
    why := "the recursive `.Applied` arm keeps strictness: `Box<int>` is NOT consistent with `Box<bool>`"
    src := "composite Box<T> { var val: T }\nprocedure u() opaque { var a: Box<int> := new Box<int>; var b: Box<bool> := a; assert 1 == 1 };" },
  { name := "tc_boxint_arg_to_boolparam", outcome := .rejected,
    why := "passing `Box<int>` to a `Box<bool>` param rejects"
    src := "composite Box<T> { var val: T }\nprocedure needsBool(b: Box<bool>) opaque { assert 1 == 1 };\nprocedure u() opaque { var a: Box<int> := new Box<int>; needsBool(a); assert 1 == 1 };" },
  { name := "tc_barename_wrong_base", outcome := .rejected,
    why := "the bare-name~instantiation arm fires only on matching bases: bare `new Dog` into `Box<int>` rejects"
    src := "composite Box<T> { var val: T }\ncomposite Dog { var a: int }\nprocedure u() opaque { var b: Box<int> := new Dog; assert 1 == 1 };" },
  { name := "tc_tvarbody_int_eq_true", outcome := .rejected,
    why := "the `.TVar` wildcard must not blanket-disable checking inside a poly body: `var y: int := true` still rejects"
    src := "procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { var y: int := true; r := x };" },
  -- proc↔composite FIXPOINT: a poly proc whose body calls another poly proc passing the
  -- generic-composite param (`outer<T>` calls `inner<T>`). The unified worklist clones
  -- `outer$int`, discovers the now-concrete `inner(b:Box<int>)` call, clones `inner$int`,
  -- rewrites. (Previously fail-loud "generic type application reached Core translation".)
  { name := "poly_proc_chain_fixpoint", outcome := .verifies,
    why := "`outer<T>` calling `inner<T>` monomorphizes through the fixpoint and verifies"
    src := outerInner ++ "procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := outer(bx); assert got == 7 };" },
  { name := "poly_proc_chain_fixpoint_wrong", outcome := .failsExactly 1,
    why := "a wrong value through the two-hop chain must FAIL — the inner clone's contract is threaded end-to-end"
    src := outerInner ++ "procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := outer(bx); assert got == 99 };" },
  { name := "poly_proc_chain_fixpoint_multi", outcome := .verifies,
    why := "the outer→inner chain at int AND bool each monomorphize independently through the fixpoint"
    src := outerInner ++ "procedure u() opaque { var bi: Box<int> := new Box<int>; bi#val := 7; var gi: int := outer(bi); var bb: Box<bool> := new Box<bool>; bb#val := true; var gb: bool := outer(bb); assert gi == 7 && gb == true };" },
  { name := "poly_proc_chain_divergent", outcome := .rejected,
    why := "an unbounded proc chain (`grow<T>` deepening via `Box<Box<T>>`) must FAIL LOUD (depth cap), not hang/emit garbage"
    src := "composite Box<T> { var val: T }\nprocedure grow<T>(b: Box<T>) returns (r: T) opaque ensures true { var bb: Box<Box<T>> := new Box<Box<T>>; var x: Box<T> := grow(bb); r := b#val };\nprocedure u() opaque { var bx: Box<int> := new Box<int>; var got: int := grow(bx); assert 1 == 1 };" },
  -- BODY-SCAN trigger: a value-`T`-signature proc that materializes a generic composite in
  -- its BODY (`var t: Box<T> := new Box<T>`) must MONOMORPHIZE, not ride freshening (which
  -- has no Core representation for a generic composite → body-local box's write would survive
  -- un-lowered → StrataBug). Found by an adversarial probe.
  { name := "poly_proc_body_local_generic_box", outcome := .verifies,
    why := "a value-T proc allocating a `Box<T>` in its BODY monomorphizes + verifies (body-scan trigger)"
    src := "composite Box<T> { var val: T }\nprocedure mkl<T>(x: T) returns (r: T) opaque ensures r == x { var t: Box<T> := new Box<T>; t#val := x; r := t#val };\nprocedure u() opaque { var got: int := mkl(7); assert got == 7 };" },
  { name := "poly_proc_body_local_generic_box_wrong", outcome := .failsExactly 1,
    why := "a wrong value from the body-local-box proc must FAIL — sound, not vacuous"
    src := "composite Box<T> { var val: T }\nprocedure mkl<T>(x: T) returns (r: T) opaque ensures r == x { var t: Box<T> := new Box<T>; t#val := x; r := t#val };\nprocedure u() opaque { var got: int := mkl(7); assert got == 8 };" },
  { name := "poly_proc_value_t_still_freshens", outcome := .verifies,
    why := "HYBRID PARTITION: a value-T proc touching NO generic composite still rides freshening (body-scan must not over-capture) — int AND bool"
    src := "procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };\nprocedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 7 && gb == true };" },
  -- An UNCALLED value-`T` poly proc (kept verbatim, NOT witness-cloned — it touches no generic
  -- composite) still has its own body VC emitted + discharged: a TRUE postcondition verifies,
  -- a FALSE one fails loud. Pins that the uncalled value-`T` path is never silently unchecked.
  { name := "poly_proc_value_t_uncalled_true", outcome := .verifies,
    why := "an uncalled value-T poly proc with a TRUE postcondition (`ensures r==x`) verifies — its body VC is checked even with no call site"
    src := "procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };\nprocedure u() opaque { assert 1 == 1 };" },
  { name := "poly_proc_value_t_uncalled_false", outcome := .failsExactly 1,
    why := "an uncalled value-T poly proc with a FALSE postcondition (`ensures r==z` but `r:=x`) must FAIL — uncalled value-T contracts are not silently unchecked"
    src := "procedure bad<T>(x: T, z: T) returns (r: T) opaque ensures r == z { r := x };\nprocedure u() opaque { assert 1 == 1 };" },
  -- Synthetic WITNESS for uncalled composite-`T` procs: an uncalled proc would be dropped at
  -- emission (0 call sites → 0 clones), leaving its contract unchecked; we clone it at a
  -- fresh opaque zero-field composite per typevar so the contract is checked at a maximally-
  -- uninterpreted stand-in.
  { name := "poly_proc_uncalled_witness_false", outcome := .failsExactly 1,
    why := "a FALSE postcondition on an UNCALLED composite-T poly proc must FAIL at the witness (was silently 0 before)"
    src := "composite Box<T> { var val: T }\nprocedure bad<T>(b: Box<T>) returns (r: int) opaque ensures r == 0 { r := 1 };\nprocedure u() opaque { assert 1 == 1 };" },
  { name := "poly_proc_uncalled_witness_true", outcome := .verifies,
    why := "a TRUE contract on an uncalled poly proc must still VERIFY (the witness must not invent a false obligation)"
    src := "composite Box<T> { var val: T }\nprocedure good<T>(b: Box<T>) returns (r: int) opaque ensures r == 0 { r := 0 };\nprocedure u() opaque { assert 1 == 1 };" },
  { name := "poly_proc_uncalled_witness_field_false", outcome := .failsExactly 1,
    why := "an uncalled proc whose body reads the WRONG box (`r == b#val` from a fresh box) must FAIL at the witness"
    src := "composite Box<T> { var val: T }\nprocedure rd<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { var t: Box<T> := new Box<T>; r := t#val };\nprocedure u() opaque { assert 1 == 1 };" },
  { name := "poly_proc_called_and_uncalled_mixed", outcome := .failsExactly 1,
    why := "a CALLED proc (real inst, no witness) + an UNCALLED false-contract proc (witness, FAILS) — witness emitted iff uncalled, exactly 1 failure"
    src := "composite Box<T> { var val: T }\nprocedure used<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };\nprocedure unused<T>(b: Box<T>) returns (r: int) opaque ensures r == 5 { r := 6 };\nprocedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := used(bx); assert got == 7 };" },
  { name := "poly_proc_uncalled_divergent_witness", outcome := .rejected,
    why := "an UNCALLED divergent poly proc must FAIL LOUD via the depth cap on the witness/second-drain path"
    src := "composite Box<T> { var val: T }\nprocedure grow<T>(b: Box<T>) returns (r: T) opaque ensures true { var bb: Box<Box<T>> := new Box<Box<T>>; var x: Box<T> := grow(bb); r := b#val };\nprocedure u() opaque { assert 1 == 1 };" },
  -- THREE uncalled procs with DISTINCT false postconditions ⇒ EXACTLY 3 failures (witness
  -- obligations counted distinctly, not merged/dropped; harness keys on `index:label`).
  { name := "poly_proc_witness_obligations_counted", outcome := .failsExactly 3,
    why := "3 uncalled procs with distinct FALSE postconditions yield EXACTLY 3 failures (no merge/drop)"
    src := "composite Box<T> { var val: T }\nprocedure b1<T>(b: Box<T>) returns (r: int) opaque ensures r == 1 { r := 0 };\nprocedure b2<T>(b: Box<T>) returns (r: int) opaque ensures r == 2 { r := 0 };\nprocedure b3<T>(b: Box<T>) returns (r: int) opaque ensures r == 3 { r := 0 };\nprocedure u() opaque { assert 1 == 1 };" },
  -- WITNESS IS NOT A SINGLETON: `ensures a#val == b#val` is FALSE in general (two boxes hold
  -- independent values) → must FAIL. If the witness sort were a singleton it would hold
  -- vacuously and mask the bug; failing ⇒ the sort has arbitrary cardinality (faithful tyvar).
  { name := "poly_proc_witness_not_singleton", outcome := .failsExactly 1,
    why := "an uncalled `ensures a#val==b#val` (false in general) must FAIL at the witness (else the witness sort is a singleton)"
    src := "composite Box<T> { var val: T }\nprocedure f<T>(a: Box<T>, b: Box<T>) returns (r: int) opaque ensures a#val == b#val { r := 0 };\nprocedure u() opaque { assert 1 == 1 };" },
  -- INDIRECT-ONLY callee gets NO redundant witness (`inner` called only from `outer`'s body;
  -- the worklist already clones `inner$int`). Soundness preserved end-to-end: true + false twin.
  { name := "poly_proc_indirect_callee_no_witness", outcome := .verifies,
    why := "an indirect-only callee chain verifies (no redundant witness, no masking)"
    src := outerInner ++ "procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := outer(bx); assert got == 7 };" },
  { name := "poly_proc_indirect_callee_no_witness_false", outcome := .failsExactly 1,
    why := "the indirect chain's false twin must FAIL"
    src := outerInner ++ "procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := outer(bx); assert got == 99 };" },
  -- A poly proc materializing a generic-composite param, called ONLY from a CONTRACT
  -- position (`invokeOn`) — not a body. The monomorphizer must SEED that call for cloning
  -- (collect over contract positions, not just bodies), else the final rewrite renames it
  -- to `g$…$int` while the clone was never emitted → dangling ref / loud Core failure.
  { name := "poly_proc_call_in_invokeon", outcome := .verifies,
    why := "a poly proc called only via `invokeOn` (a contract position) is seeded + cloned, not just renamed (else `g$a1$int` dangles)"
    src := "composite Box<T> { var val: T }\nprocedure g<T>(b: Box<T>) opaque { assert 1 == 1 };\nprocedure h(x: Box<int>)\n  invokeOn g(x)\n  opaque\n{ assert 1 == 1 };" } ]

/-- Polymorphic procedures: freshening + monomorphization, abort-mask freedom, cross-slot
    coupling, witness-checked uncalled contracts, and #1121 reject-side coexistence. -/
def runPolyProcedureTests : IO Unit := checkCases polyProcedureCorpus

#guard_msgs (drop info, error) in
#eval runPolyProcedureTests

/-! ## Generic composites verify end-to-end (monomorphization)

`composite Box<T>` is lowered by emitting one concrete composite per used
instantiation (`Box$int`, `Box$bool`) and rewriting `Box<int>` type references +
`new Box` allocations to the monomorphic name. Proven: single instantiation with
field write/read, and two distinct instantiations coexisting. -/
def genericBoxProgram := r"
composite Box<T> { var val: T }

procedure useBox()
  opaque
{
    var b: Box<int> := new Box;
    b#val := 42;
    assert b#val == 42
};"

def genericBoxMultiProgram := r"
composite Box<T> { var val: T }

procedure useTwo()
  opaque
{
    var a: Box<int> := new Box;
    a#val := 7;
    var b: Box<bool> := new Box;
    b#val := true;
    assert a#val == 7
};"

def genericCompositeCorpus : List Case := [
  { name := "generic_box", outcome := .verifies,
    why := "composite Box<T> instantiated at Box<int> monomorphizes + verifies"
    src := genericBoxProgram },
  { name := "generic_box_multi", outcome := .verifies,
    why := "two instantiations (Box<int>+Box<bool>) monomorphize independently"
    src := genericBoxMultiProgram },
  -- SOUNDNESS GUARD: an arg the mangler can't tag injectively (`Box<Map int int>`) must
  -- FAIL LOUD, never silently coalesce with another instantiation under a collapsed name.
  { name := "untaggable_arg", outcome := .rejected,
    why := "`Box<Map int int>` (un-taggable arg) must fail loud, not coalesce"
    src := "composite Box<T> { var val: T }\nprocedure u() opaque { var a: Box<Map int int> := new Box; assert 1 == 1 };" },
  -- A generic over a COLLECTION type (`Map K V`): the consistency relation recurses into
  -- `.TMap` element-wise (like `.Applied`) so a concrete `Map int bool` argument satisfies a
  -- `Map K V` parameter — the nested `int`/`bool` reach the `.TVar` wildcard. Without the
  -- `.TMap` consistency arm this was spuriously over-rejected ("expected 'Map K V', got
  -- 'Map int bool'"). The `ensures r == m` makes the accept OBSERVABLE (a real obligation),
  -- not just translatable; the strictness twin pins that concrete-vs-concrete stays strict.
  { name := "generic_map_param", outcome := .verifies,
    why := "a concrete `Map int bool` into a generic `Map K V` proc param verifies, returned map observed via `ensures r == m`"
    src := "procedure idm<K,V>(m: Map K V) returns (r: Map K V) opaque ensures r == m { r := m };\nprocedure u() opaque { var mm: Map int bool; var rr: Map int bool := idm(mm); assert rr == mm };" },
  { name := "generic_map_param_wrong", outcome := .failsExactly 1,
    why := "the returned map equals `mm`, not the unrelated `nn` — `assert rr == nn` must FAIL (accept is sound, not vacuous)"
    src := "procedure idm<K,V>(m: Map K V) returns (r: Map K V) opaque ensures r == m { r := m };\nprocedure u() opaque { var mm: Map int bool; var nn: Map int bool; var rr: Map int bool := idm(mm); assert rr == nn };" },
  { name := "map_concrete_mismatch", outcome := .rejected,
    why := "STRICTNESS: a concrete `Map int int` into a `Map int bool` param must be REJECTED — the `.TMap` arm recurses but stays strict on concrete leaves (no hole opened)"
    src := "procedure needsIB(m: Map int bool) opaque { assert 1 == 1 };\nprocedure u() opaque { var mm: Map int int; needsIB(mm); assert 1 == 1 };" },
  -- Generic-composite instantiation in type positions beyond the original three (field /
  -- proc in-out / body Declare); the monomorphizer now collects+rewrites every position.
  { name := "generic_in_datatype", outcome := .verifies,
    why := "Box<int> as a datatype ctor arg is collected + rewritten"
    src := "composite Box<T> { var val: T }\ndatatype Wrap { MkWrap(b: Box<int>) }\nprocedure u() opaque { assert 1 == 1 };" },
  { name := "generic_in_quant", outcome := .verifies,
    why := "forall over a Box<int> binder translates"
    src := "composite Box<T> { var val: T }\nprocedure u() opaque { var p: bool := forall(b: Box<int>) => true; assert p };" },
  { name := "generic_in_quant_wrong", outcome := .failsExactly 1,
    why := "a FALSE quantified claim over a Box<int> binder must FAIL — sound, not vacuous"
    src := "composite Box<T> { var val: T }\nprocedure u() opaque { var p: bool := forall(b: Box<int>) => false; assert p };" },
  -- A standalone declaration WITHOUT an initializer (`var b: Box<int>;`) parses to
  -- `.Var (.Declare …)`, NOT the `.Assign [.Declare …] e` form — a distinct statement-type
  -- slot the monomorphizer's `stmtTypeSlots`/`rewriteStmt` must also cover, else `Box<int>`
  -- survives un-lowered to Core.
  { name := "generic_decl_no_init", outcome := .verifies,
    why := "a no-initializer generic decl `var b: Box<int>;` must lower (be collected + rewritten), not survive un-lowered to Core"
    src := "composite Box<T> { var val: T }\nprocedure u() opaque { var b: Box<int>; assert 1 == 1 };" },
  -- A generic instantiation in a CONTRACT (precondition quantifier binder), not the body —
  -- the monomorphizer's collect + final rewrite must reach precondition/decreases/invokeOn
  -- positions, not only procedure bodies.
  { name := "generic_in_precondition", outcome := .verifies,
    why := "`Box<int>` in a precondition quantifier binder must be collected + rewritten (contract positions, not just body)"
    src := "composite Box<T> { var val: T }\nprocedure u()\n  requires forall(b: Box<int>) => true\n  opaque\n{ assert 1 == 1 };" },
  -- Field SELECT inside a quantifier BODY (a triggerless quantifier's body was skipped by
  -- heap-read analysis — a do-block sequencing bug — so `c#v` survived to fail at translation).
  { name := "quant_body_field", outcome := .verifies,
    why := "a TRUE field-read fact in a quantifier body verifies (heap-read-in-body fix)"
    src := "composite C { var v: int }\nprocedure u() opaque { var p: bool := forall(c: C) => c#v == c#v; assert p };" },
  { name := "quant_body_field_wrong", outcome := .failsExactly 1,
    why := "a FALSE field-read fact in a quantifier body must FAIL — sound, not vacuous"
    src := "composite C { var v: int }\nprocedure u() opaque { var p: bool := forall(c: C) => c#v == 5; assert p };" },
  { name := "untaggable_in_datatype", outcome := .rejected,
    why := "`Box<Map int int>` as a datatype ctor arg must fail loud in EVERY position, not just var-decls"
    src := "composite Box<T> { var val: T }\ndatatype Wrap { MkWrap(b: Box<Map int int>) }\nprocedure u() opaque { assert 1 == 1 };" },
  -- NESTED GENERICS: a composite whose field is a generic instantiation of the same param
  -- (`Pair<T> { b: Box<T> }`). (A) sound when the inner inst is also named directly.
  { name := "nested_generic", outcome := .verifies,
    why := "Pair<int> with field Box<int> (Box<int> also named) resolves + verifies"
    src := "composite Box<T> { var val: T }\ncomposite Pair<T> { var b: Box<T> }\nprocedure u() opaque { var inner: Box<int> := new Box; inner#val := 5; var p: Pair<int> := new Pair; p#b := inner; var got: Box<int> := p#b; assert got#val == 5 };" },
  { name := "nested_generic_wrong", outcome := .failsExactly 1,
    why := "a FALSE read of the nested field must FAIL — sound, not vacuous"
    src := "composite Box<T> { var val: T }\ncomposite Pair<T> { var b: Box<T> }\nprocedure u() opaque { var inner: Box<int> := new Box; inner#val := 5; var p: Pair<int> := new Pair; p#b := inner; var got: Box<int> := p#b; assert got#val == 6 };" },
  -- (B) the fixpoint worklist: inner inst reachable ONLY through the outer's substituted
  -- field (`q#b := p#b`, Box<int> named nowhere else) is now discovered + emitted.
  { name := "nested_generic_via_field_only", outcome := .verifies,
    why := "`q#b := p#b` (inner Box<int> reachable only via the field) translates (fixpoint worklist)"
    src := "composite Box<T> { var val: T }\ncomposite Pair<T> { var b: Box<T> }\nprocedure u() opaque { var p: Pair<int> := new Pair; var q: Pair<int> := new Pair; q#b := p#b; assert 1 == 1 };" },
  { name := "nested_generic_via_field_wrong", outcome := .failsExactly 1,
    why := "a FALSE read of the field-only-reachable nested monomorph must FAIL — sound, not vacuous"
    src := "composite Box<T> { var val: T }\ncomposite Pair<T> { var b: Box<T> }\nprocedure u() opaque { var p: Pair<int> := new Pair; var inner: Box<int> := new Box; inner#val := 7; p#b := inner; var got: Box<int> := p#b; assert got#val == 8 };" },
  -- TERMINATION + clean rejection: a divergent recursive generic (`L<T>{ next: L<L<T>> }`)
  -- is cut off at the depth bound and rejected LOUD — not a hang, not dead monomorphs.
  { name := "recursive_generic_rejected", outcome := .rejected,
    why := "divergent `L<L<T>>` must be REJECTED with a clear diagnostic (the test completing proves termination)"
    src := "composite L<T> { var next: L<L<T>> }\nprocedure u() opaque { var x: L<int> := new L; assert 1 == 1 };" },
  -- EXPLICIT `new C<τ>` SYNTAX: allocation carries its instantiation, so it works in every
  -- position incl. field-write + call-arg (which previously crashed in Core on `C_TypeTag`).
  { name := "new_typeargs_field", outcome := .verifies,
    why := "`new Box<int>` in a field-write context verifies (was a Box_TypeTag crash)"
    src := "composite Box<T> { var val: T }\ncomposite Holder { var b: Box<int> }\nprocedure u() opaque { var h: Holder := new Holder; var inner: Box<int> := new Box<int>; inner#val := 7; h#b := inner; var got: Box<int> := h#b; assert got#val == 7 };" },
  { name := "new_typeargs_field_wrong", outcome := .failsExactly 1,
    why := "a FALSE read after `new Box<int>` field write must FAIL"
    src := "composite Box<T> { var val: T }\ncomposite Holder { var b: Box<int> }\nprocedure u() opaque { var h: Holder := new Holder; var inner: Box<int> := new Box<int>; inner#val := 7; h#b := inner; var got: Box<int> := h#b; assert got#val == 8 };" },
  { name := "new_typeargs_arg", outcome := .verifies,
    why := "`new Box<int>` as a call argument verifies (also previously crashed)"
    src := "composite Box<T> { var val: T }\nprocedure take(x: Box<int>) opaque { assert 1 == 1 };\nprocedure u() opaque { take(new Box<int>); assert 1 == 1 };" },
  { name := "new_typeargs_two_inst", outcome := .verifies,
    why := "two explicit `new Box<τ>` instantiations pick DISTINCT monomorphs (no coalescing)"
    src := "composite Box<T> { var val: T }\nprocedure u() opaque { var a: Box<int> := new Box<int>; a#val := 5; var b: Box<bool> := new Box<bool>; b#val := true; assert a#val == 5 };" },
  -- ARITY: an explicit `new C<τ…>` must supply exactly the composite's declared type-arg
  -- count. Surplus args would otherwise be silently dropped by the monomorphizer's `zip`.
  { name := "new_typeargs_wrong_arity", outcome := .rejected,
    why := "`new Box<int,bool>` for a single-param `Box<T>` must be REJECTED (type-arg arity check)"
    src := "composite Box<T> { var val: T }\nprocedure u() opaque { var b: Box<int, bool> := new Box<int, bool>; b#val := 7; assert b#val == 7 };" },
  { name := "new_bare_legacy", outcome := .verifies,
    why := "bare `new Box` in the legacy `var x: C<τ> := new C` form still works (args from declared type)"
    src := "composite Box<T> { var val: T }\nprocedure u() opaque { var b: Box<int> := new Box; b#val := 1; assert b#val == 1 };" },
  -- SELF-SEEDING: `new Box<bool>` is the SOLE mention of Box<bool> (generic sink, no type
  -- annotation seeds it) — the monomorph must be collected from the allocation site itself.
  { name := "new_typeargs_self_seed", outcome := .verifies,
    why := "`new Box<bool>` as the sole mention (via a generic sink) is collected + verifies (collect/rewrite agree)"
    src := "composite Box<T> { var val: T }\nfunction sink<T>(x: T): int { 0 };\nprocedure u() opaque { var r: int := sink(new Box<bool>); assert r == 0 };" },
  -- CHAINED field WRITE `o#i#v := …` via the dedicated `FieldPath` grammar category (a
  -- separate category from `StmtExpr` so it can't collide with a `multiAssign` value).
  { name := "chained_field_write", outcome := .verifies,
    why := "`o#i#v := 5` then read verifies (chained-write via FieldPath)"
    src := "composite Inner { var v: int }\ncomposite Outer { var i: Inner }\nprocedure u() opaque { var o: Outer := new Outer; var x: Inner := new Inner; o#i := x; o#i#v := 5; assert o#i#v == 5 };" },
  { name := "chained_field_write_wrong", outcome := .failsExactly 1,
    why := "a FALSE read after `o#i#v := 5` must FAIL — chained write is sound, not vacuous"
    src := "composite Inner { var v: int }\ncomposite Outer { var i: Inner }\nprocedure u() opaque { var o: Outer := new Outer; var x: Inner := new Inner; o#i := x; o#i#v := 5; assert o#i#v == 6 };" },
  -- Regression guard: a `multiAssign` value may be a CALL (`assign t := f()`); the FieldPath
  -- category must NOT compete with it (an `obj: StmtExpr` form mis-parsed `f()` as a field obj).
  { name := "multiassign_call_value", outcome := .verifies,
    why := "`assign var x, var y := two()` parses + translates (FieldPath must not collide with the value)"
    src := "procedure two() returns (a: int, b: int) opaque ensures a == 1 ensures b == 2 { a := 1; b := 2 };\nprocedure u() opaque { assign var x: int, var y: int := two(); assert x == 1 };" } ]

/-- Generic composites verify end-to-end via monomorphization — across every type position,
    nested generics (fixpoint worklist), explicit `new C<τ>`, and chained field writes. -/
def runGenericCompositeTest : IO Unit := checkCases genericCompositeCorpus

#guard_msgs (drop info, error) in
#eval runGenericCompositeTest

/-! ## Generic datatypes verify end-to-end (native Core parametric datatypes)

Unlike generic composites (which monomorphize to dodge the SMT wall), generic datatypes
map to NATIVE Core parametric datatypes (`declare-datatypes` with sort params) — a
pass-through, no monomorphization. Front-end plumbing: `datatype Bx<T> { … }` grammar
binder → `DatatypeDefinition.typeArgs` → resolution scopes `T` as `.TVar` → `translateType`
lowers `Bx<int>` to `.tcons "Bx" [int]`.

NB: avoid the type name `Box` here — it collides with the internal heap boxed-value
datatype from `HeapParameterization` (a pre-existing name clash, not a generics issue),
so these use `Bx`/`Lst`/`Pr`. -/
def genericDatatypeCorpus : List Case := [
  { name := "generic_datatype_construct_eq", outcome := .verifies,
    why := "a generic datatype `Bx<int>` constructed + compared verifies (native Core parametric datatype)"
    src := "datatype Bx<T> { MkBx(v: T) }\nprocedure u() opaque { var b1: Bx<int> := MkBx(5); var b2: Bx<int> := MkBx(5); assert b1 == b2 };" },
  { name := "generic_datatype_construct_eq_wrong", outcome := .failsExactly 1,
    why := "distinct `Bx<int>` values must NOT be equal — datatype eq is real, not vacuous"
    src := "datatype Bx<T> { MkBx(v: T) }\nprocedure u() opaque { var b1: Bx<int> := MkBx(5); var b2: Bx<int> := MkBx(6); assert b1 == b2 };" },
  -- Native parametric datatype = ONE declaration shared by both instances (no per-inst
  -- clone). Reads each value back so it proves distinct correct values, not just translation.
  { name := "generic_datatype_multi_instantiation", outcome := .verifies,
    why := "`Bx<int>` AND `Bx<bool>` in one program each hold their value (one shared datatype)"
    src := "datatype Bx<T> { MkBx(v: T) }\nprocedure u() opaque { var bi: Bx<int> := MkBx(5); var bb: Bx<bool> := MkBx(true); assert bi == MkBx(5) && bb == MkBx(true) };" },
  { name := "generic_datatype_recursive", outcome := .verifies,
    why := "recursive generic datatype `Lst<int>` (Cons/Nil) round-trips"
    src := "datatype Lst<T> { Nil(), Cons(head: T, tail: Lst<T>) }\nprocedure u() opaque { var xs: Lst<int> := Cons(1, Nil()); assert 1 == 1 };" },
  { name := "generic_datatype_monomorphic_unaffected", outcome := .verifies,
    why := "a datatype with NO type params still works after the grammar gained Option TypeParams"
    src := "datatype Pr { MkPr(a: int, b: int) }\nprocedure u() opaque { var p1: Pr := MkPr(1, 2); var p2: Pr := MkPr(1, 2); assert p1 == p2 };" },
  -- CROSS-INSTANTIATION DISTINCTNESS: `Bx<int>` and `Bx<bool>` are DISTINCT sorts, not
  -- erased to one — assigning across is rejected. This is what "escapes the SMT wall" means.
  { name := "generic_datatype_cross_instantiation_rejected", outcome := .rejected,
    why := "assigning `Bx<int>` to a `Bx<bool>` var must be REJECTED (distinct sorts; cross-inst confusion = unsound)"
    src := "datatype Bx<T> { MkBx(v: T) }\nprocedure u() opaque { var bi: Bx<int> := MkBx(5); var bb: Bx<bool> := bi; assert 1 == 1 };" },
  -- HEAP-STORED COMPOSITE FIELD: a generic datatype as a composite field routes through
  -- HeapParameterization's box wrapper (the `.Applied` arm — one box variant per inst).
  { name := "generic_datatype_composite_field", outcome := .verifies,
    why := "`Bx<int>` as a composite field, written + read back, verifies (heap-box `.Applied` arm)"
    src := "datatype Bx<T> { MkBx(v: T) }\ncomposite Holder { var b: Bx<int> }\nprocedure u() opaque { var h: Holder := new Holder; var x: Bx<int> := MkBx(9); h#b := x; var y: Bx<int> := h#b; assert y == x };" },
  { name := "generic_datatype_composite_field_wrong", outcome := .failsExactly 1,
    why := "a FALSE read-back of a generic-datatype field must FAIL — heap-box round-trip is sound, not vacuous"
    src := "datatype Bx<T> { MkBx(v: T) }\ncomposite Holder { var b: Bx<int> }\nprocedure u() opaque { var h: Holder := new Holder; var x: Bx<int> := MkBx(9); var z: Bx<int> := MkBx(8); h#b := x; var y: Bx<int> := h#b; assert y == z };" },
  { name := "generic_datatype_composite_two_insts", outcome := .verifies,
    why := "`Bx<int>` and `Bx<bool>` as separate composite fields each get a distinct heap-box variant"
    src := "datatype Bx<T> { MkBx(v: T) }\ncomposite Holder { var bi: Bx<int> var bb: Bx<bool> }\nprocedure u() opaque { var h: Holder := new Holder; h#bi := MkBx(1); h#bb := MkBx(true); var yi: Bx<int> := h#bi; assert yi == MkBx(1) };" } ]

/-- Generic DATATYPES. Unlike generic composites (which monomorphize to dodge the SMT
    wall), generic datatypes map to NATIVE Core parametric datatypes (`declare-datatypes`
    with sort params) — a pass-through, no monomorphization. -/
def runGenericDatatypeTest : IO Unit := checkCases genericDatatypeCorpus

#guard_msgs (drop info, error) in
#eval runGenericDatatypeTest

/-! ## Generic composite methods (instance procedures), inheritance, upcasting

A method on a generic composite — `composite Box<T> { var val: T; procedure
get(self: Box<T>) returns (r: T) … }` — is lifted (by `liftInstanceProceduresPass`,
moved before monomorphization) to a top-level POLY procedure carrying the composite's
type params (`Box$get<T>(self: Box<T>)`), which the procedure monomorphizer then
clones per call-site instantiation. So methods reuse the procedure-monomorphization
machinery with no new monomorphization. `extends` on a generic composite is still
rejected loud. -/
private def boxGet := "composite Box<T> {\n  var val: T\n  procedure get(self: Box<T>) returns (r: T) opaque ensures r == self#val { r := self#val };\n}\n"

-- Methods on generic composites lift to poly procedures (carrying the composite's type
-- params, plus the method's own); the procedure monomorphizer then handles them per call
-- site. Inheritance monomorphizes the child + parent (concrete or generic parent), topo-
-- ordering the parent monomorph first. Upcast subtyping is REMAP-AWARE via
-- `substitutedAncestors` (an earlier non-substituting version accepted the WRONG supertype
-- — UNSOUND; these pin both the correct upcasts AND that the wrong targets are rejected).
-- Field-type concretization is reject-only: a `.TVar` field is checked against the holder's
-- concrete instantiation, so a wrong access rejects while correct/polymorphic ones translate.
def genericMethodCorpus : List Case := [
  { name := "generic_method_get", outcome := .verifies,
    why := "`Box<T>.get` reading `self#val` at int verifies (method lift + monomorphization)"
    src := boxGet ++ "procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := bx#get(); assert got == 7 };" },
  { name := "generic_method_get_wrong", outcome := .failsExactly 1,
    why := "a wrong value via `bx#get()` must FAIL — the field read is real, not vacuous"
    src := boxGet ++ "procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := bx#get(); assert got == 8 };" },
  { name := "generic_method_get_multi", outcome := .verifies,
    why := "`Box<T>.get` at int AND bool each monomorphize independently (clone id-clearing)"
    src := boxGet ++ "procedure u() opaque { var bi: Box<int> := new Box<int>; bi#val := 7; var gi: int := bi#get(); var bb: Box<bool> := new Box<bool>; bb#val := true; var gb: bool := bb#get(); assert gi == 7 && gb == true };" },
  { name := "generic_method_false_postcondition", outcome := .failsExactly 1,
    why := "a method with a FALSE `ensures` must FAIL — contract genuinely checked, not vacuous"
    src := "composite Box<T> {\n  var val: T\n  procedure bad(self: Box<T>) returns (r: int) opaque ensures r == 0 { r := 1 };\n}\nprocedure u() opaque { var bx: Box<int> := new Box<int>; var g: int := bx#bad(); assert 1 == 1 };" },
  { name := "generic_method_precond_gated", outcome := .failsAtLeast 1,
    why := "a violated precondition on `self#val` (caller sets 5, method requires 7) must GATE"
    src := "composite Box<T> {\n  var val: T\n  procedure get7(self: Box<T>) returns (r: T) requires self#val == 7 opaque ensures r == self#val { r := self#val };\n}\nprocedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 5; var g: int := bx#get7(); assert 1 == 1 };" },
  -- A method declaring its OWN type param `<U>`, distinct from the composite's `T`: the
  -- lift carries BOTH (composite's ++ method's), monomorphized per call.
  { name := "method_own_typaram", outcome := .verifies,
    why := "a method's own type param `id2<U>` called at bool verifies (`U` binds to `bool`)"
    src := "composite Box<T> {\n  var v: T\n  procedure id2<U>(self: Box<T>, x: U) returns (r: U) opaque ensures r == x { r := x };\n}\nprocedure u() opaque { var b: Box<int> := new Box<int>; var y: bool := b#id2(true); assert y == true };" },
  { name := "method_own_typaram_wrong", outcome := .failsExactly 1,
    why := "a FALSE postcondition on a method-own-typaram method must FAIL — sound, not vacuous"
    src := "composite Box<T> {\n  var v: T\n  procedure bad<U>(self: Box<T>, x: U) returns (r: int) opaque ensures r == 0 { r := 1 };\n}\nprocedure u() opaque { var b: Box<int> := new Box<int>; var z: int := b#bad(true); assert 1 == 1 };" },
  { name := "method_own_typaram_multi", outcome := .verifies,
    why := "a method-own type param at int AND bool each monomorphize + verify"
    src := "composite Box<T> {\n  var v: T\n  procedure id2<U>(self: Box<T>, x: U) returns (r: U) opaque ensures r == x { r := x };\n}\nprocedure u() opaque { var b: Box<int> := new Box<int>; var p: int := b#id2(7); var q: bool := b#id2(false); assert p == 7 && q == false };" },
  -- Inheritance — concrete parent (`Box<T> extends Base`): child monomorphizes to
  -- `Box$int extends Base`, emitted AFTER the parent so re-resolution builds the parent's
  -- field-inheritance scope first (the parent-before-child emission-order fix).
  { name := "generic_extends_concrete_parent", outcome := .verifies,
    why := "`Box<T> extends Base` (concrete parent) monomorphizes + inherits `tag`, verifies"
    src := "composite Base { var tag: int }\ncomposite Box<T> extends Base { var val: T }\nprocedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 1; b#val := 7; assert b#tag == 1 && b#val == 7 };" },
  { name := "generic_extends_concrete_parent_wrong", outcome := .failsExactly 1,
    why := "a wrong INHERITED-field value must FAIL — checked, not vacuously havoc'd (the bug fixed here)"
    src := "composite Base { var tag: int }\ncomposite Box<T> extends Base { var val: T }\nprocedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 1; assert b#tag == 2 };" },
  -- Inheritance — generic parent at an instantiation (`Box<T> extends Base<T>`): the
  -- monomorphizer collects the parent inst and topo-orders `Base$int` before `Box$int`.
  -- Needed for idiomatic Java (generic-class-extends-generic-class).
  { name := "generic_extends_generic_parent", outcome := .verifies,
    why := "`Box<T> extends Base<T>` → `Box$int extends Base$int`, inherits `tag:T`→int, verifies"
    src := "composite Base<T> { var tag: T }\ncomposite Box<T> extends Base<T> { var val: T }\nprocedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 1; b#val := 7; assert b#tag == 1 && b#val == 7 };" },
  { name := "generic_extends_generic_parent_wrong", outcome := .failsExactly 1,
    why := "a wrong value on the generic-parent's inherited field must FAIL"
    src := "composite Base<T> { var tag: T }\ncomposite Box<T> extends Base<T> { var val: T }\nprocedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 1; assert b#tag == 2 };" },
  { name := "generic_extends_generic_parent_multi", outcome := .verifies,
    why := "`Box<int>`/`Box<bool>` get distinct parent monomorphs `Base$int`/`Base$bool`"
    src := "composite Base<T> { var tag: T }\ncomposite Box<T> extends Base<T> { var val: T }\nprocedure u() opaque { var bi: Box<int> := new Box<int>; bi#tag := 9; var bb: Box<bool> := new Box<bool>; bb#tag := true; assert bi#tag == 9 && bb#tag == true };" },
  -- Generic upcast — same-instantiation, reads the inherited field back through the parent.
  { name := "generic_upcast_same_inst", outcome := .verifies,
    why := "`Box<int>` → `Base<int>` (same-inst upcast) verifies, reading the inherited tag"
    src := "composite Base<T> { var tag: T }\ncomposite Box<T> extends Base<T> { var val: T }\nprocedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 5; var p: Base<int> := b; assert p#tag == 5 };" },
  -- REMAP upcast: `P2<A,B> extends Pair<B,A>` so `P2<int,bool>`'s parent is `Pair<bool,int>`
  -- (inherited `fst:bool`, `snd:int`). Reads values back through the parent — guards
  -- VALUE-PRESERVATION through the remap, the exact property the reverted unsound upcast broke.
  { name := "generic_upcast_remap", outcome := .verifies,
    why := "`P2<int,bool>` → `Pair<bool,int>` verifies with values preserved through the remap"
    src := "composite Pair<A,B> { var fst: A var snd: B }\ncomposite P2<A,B> extends Pair<B,A> { var extra: int }\nprocedure u() opaque { var x: P2<int,bool> := new P2<int,bool>; x#fst := true; x#snd := 9; var p: Pair<bool,int> := x; assert p#fst == true && p#snd == 9 };" },
  { name := "generic_upcast_remap_wrong_value", outcome := .failsExactly 1,
    why := "a WRONG value read back through the remapped upcast must FAIL (not vacuous)"
    src := "composite Pair<A,B> { var fst: A var snd: B }\ncomposite P2<A,B> extends Pair<B,A> { var extra: int }\nprocedure u() opaque { var x: P2<int,bool> := new P2<int,bool>; x#snd := 9; var p: Pair<bool,int> := x; assert p#snd == 8 };" },
  -- CONCRETIZATION upcast: `Box<T> extends Base<int>` so `Box<bool>`'s parent is `Base<int>`.
  { name := "generic_upcast_concretization", outcome := .verifies,
    why := "`Box<bool> extends Base<int>` → `Base<int>` verifies with the concretized field preserved"
    src := "composite Base<S> { var b: S }\ncomposite Box<T> extends Base<int> { var v: T }\nprocedure u() opaque { var x: Box<bool> := new Box<bool>; x#b := 7; var p: Base<int> := x; assert p#b == 7 };" },
  { name := "generic_upcast_concretization_wrong_value", outcome := .failsExactly 1,
    why := "a WRONG concretized-field value must FAIL"
    src := "composite Base<S> { var b: S }\ncomposite Box<T> extends Base<int> { var v: T }\nprocedure u() opaque { var x: Box<bool> := new Box<bool>; x#b := 7; var p: Base<int> := x; assert p#b == 6 };" },
  -- Upcast MUST-REJECTs — the unsoundnesses the adversarial pass found, now closed.
  { name := "generic_upcast_wrong_inst", outcome := .rejected,
    why := "`Box<int>` into a `Base<bool>` var must be REJECTED (wrong instantiation)"
    src := "composite Base<T> { var tag: T }\ncomposite Box<T> extends Base<T> { var val: T }\nprocedure u() opaque { var b: Box<int> := new Box<int>; var p: Base<bool> := b; assert 1 == 1 };" },
  { name := "generic_upcast_remap_wrong_target", outcome := .rejected,
    why := "`P2<int,bool> extends Pair<B,A>` upcast to the WRONG `Pair<int,bool>` (true supertype `Pair<bool,int>`) must be REJECTED — the unsound wrong-accept that ignored the extends remap"
    src := "composite Pair<A,B> { var fst: A var snd: B }\ncomposite P2<A,B> extends Pair<B,A> { var extra: int }\nprocedure u() opaque { var x: P2<int,bool> := new P2<int,bool>; var p: Pair<int,bool> := x; assert 1 == 1 };" },
  { name := "generic_upcast_concretization_wrong_target", outcome := .rejected,
    why := "`Box<bool> extends Base<int>` upcast to `Base<bool>` must be REJECTED (supertype is `Base<int>`) — the other concretization wrong-accept"
    src := "composite Base<S> { var b: S }\ncomposite Box<T> extends Base<int> { var v: T }\nprocedure u() opaque { var x: Box<bool> := new Box<bool>; var p: Base<bool> := x; assert 1 == 1 };" },
  { name := "generic_upcast_unrelated", outcome := .rejected,
    why := "`Box<int>` into an UNRELATED `Other<int>` var must be REJECTED"
    src := "composite Other<T> { var o: T }\ncomposite Base<T> { var tag: T }\ncomposite Box<T> extends Base<T> { var val: T }\nprocedure u() opaque { var b: Box<int> := new Box<int>; var p: Other<int> := b; assert 1 == 1 };" },
  -- DIAMOND on a GENERIC receiver: a field inherited via two paths (`D<T>` extends both
  -- `L<T>` and `R<T>`, each extending `Top<T>`) is ambiguous and the access must be REJECTED.
  -- The receiver is `D<int>` (an `.Applied` type), so the diamond check must peel the base
  -- name — else the access is missed pre-monomorphization and surfaces as an internal error
  -- when the monomorph re-resolves. This pins the clean rejection on a generic receiver.
  { name := "diamond_field_generic_receiver", outcome := .rejected,
    why := "a diamond-inherited field read on a generic receiver `D<int>` must be REJECTED cleanly (peel `.Applied` to base name), not an internal error"
    src := "composite Top<T> { var f: T }\ncomposite L<T> extends Top<T> { }\ncomposite R<T> extends Top<T> { }\ncomposite D<T> extends L<T>, R<T> { }\nprocedure u() opaque { var d: D<int> := new D<int>; var x: int := d#f; assert 1 == 1 };" },
  -- Field-type concretization (reject-only): a `.TVar` field is checked against the holder's
  -- concrete instantiation by substituting the DECLARING composite's params (own field: holder
  -- args; inherited: via `substitutedAncestors`, remap-aware). Can never create a false accept;
  -- the IDENTITY on polymorphic code (holder at `.TVar` args ⇒ field stays `.TVar`).
  { name := "field_tvar_own_write_wrong", outcome := .rejected,
    why := "writing an `Other` into `g#h` (g: GHolder<Pair<int,bool>>, field `h:T` = `Pair<int,bool>`) must be REJECTED"
    src := "composite Pair<X,Y> { var a: X var b: Y }\ncomposite Other { var z: int }\ncomposite GHolder<T> { var h: T }\nprocedure u(g: GHolder<Pair<int,bool>>) opaque modifies g { var o: Other := new Other; g#h := o };" },
  { name := "field_tvar_own_read_wrong", outcome := .rejected,
    why := "reading `g#h` (= `Pair<int,bool>`) into an `Other` local must be REJECTED"
    src := "composite Pair<X,Y> { var a: X var b: Y }\ncomposite Other { var z: int }\ncomposite GHolder<T> { var h: T }\nprocedure u(g: GHolder<Pair<int,bool>>) opaque { var o: Other := g#h };" },
  { name := "field_tvar_inherited_write_wrong", outcome := .rejected,
    why := "writing `Other` into inherited `g#h` (Base<T>.h = `Pair<int,bool>`) must be REJECTED (inherited concretization)"
    src := "composite Pair<X,Y> { var a: X var b: Y }\ncomposite Other { var z: int }\ncomposite Base<T> { var h: T }\ncomposite GHolder<T> extends Base<T> { var k: int }\nprocedure u(g: GHolder<Pair<int,bool>>) opaque modifies g { var o: Other := new Other; g#h := o };" },
  { name := "field_tvar_own_correct", outcome := .verifies,
    why := "writing/reading a `Pair<int,bool>` through `g#h` (correct type) must STILL translate (not over-rejected)"
    src := "composite Pair<X,Y> { var a: X var b: Y }\ncomposite GHolder<T> { var h: T }\nprocedure u(g: GHolder<Pair<int,bool>>) opaque modifies g { var p: Pair<int,bool> := new Pair<int,bool>; g#h := p; var q: Pair<int,bool> := g#h; assert 1 == 1 };" },
  { name := "field_tvar_inherited_correct", outcome := .verifies,
    why := "writing a `Pair<int,bool>` through inherited `g#h` (correct type) must STILL translate"
    src := "composite Pair<X,Y> { var a: X var b: Y }\ncomposite Base<T> { var h: T }\ncomposite GHolder<T> extends Base<T> { var k: int }\nprocedure u(g: GHolder<Pair<int,bool>>) opaque modifies g { var p: Pair<int,bool> := new Pair<int,bool>; g#h := p; assert 1 == 1 };" },
  -- Remap stays sound through concretization: `GHolder<A,B> extends Base<B,A>`, inherited
  -- `h:U` (Base<U,V>) at `GHolder<int,bool>` is `bool`; writing `7` (int) must reject.
  { name := "field_tvar_inherited_remap_write_wrong", outcome := .rejected,
    why := "with the `extends Base<B,A>` remap, inherited `g#h` at `GHolder<int,bool>` is `bool`; writing `7` must be REJECTED"
    src := "composite Base<U,V> { var h: U }\ncomposite GHolder<A,B> extends Base<B,A> { var k: int }\nprocedure u(g: GHolder<int,bool>) opaque modifies g { g#h := 7 };" } ]

/-- Generic composite METHODS, inheritance, upcasting, and field-type concretization. -/
def runGenericMethodTest : IO Unit := checkCases genericMethodCorpus

#guard_msgs (drop info, error) in
#eval runGenericMethodTest

/-! ## Reference-kinded T through a function: already works (no erasure pass needed)

Empirically established (this commit): a polymorphic `function id<T>` applied to a
**composite (reference) argument** verifies, because every composite lowers to the
single `tcons "Composite"` type and Core's HM unifies `ftvar T` with `Composite`
exactly as it does with `int`. The pass-through path is therefore *kind-agnostic*
— there is NO separate "erase reference T to Composite" pass to write for
functions. (Reference T only needs special handling where it would reach machinery
that can't represent a type variable: a composite FIELD of type T → monomorphization;
a polymorphic procedure → per-call-site freshening. Neither is an erasure pass.) -/
def polyRefFunctionProgram := r"
composite Cir { var r: int }

function idc<T>(x: T): T { x };

procedure useRef()
  opaque
{
    var c: Cir := new Cir;
    c#r := 7;
    var d: Cir := idc(c);
    assert d#r == 7
};"

def runPolyRefFunctionTest : IO Unit := do
  let m ← corpusMetricsOf "poly_ref_fn" polyRefFunctionProgram
  IO.println (serializeMetrics "poly_ref_fn" m)
  unless m.translated do
    throw (IO.userError "poly_ref_fn: a polymorphic function over a REFERENCE arg failed to translate — the ftvar/Composite unification regressed")
  unless m.numFailures == 0 do
    throw (IO.userError s!"poly_ref_fn: expected all-verified, got numFailures={m.numFailures}")

#guard_msgs (drop info, error) in
#eval runPolyRefFunctionTest

end Strata.Laurel
