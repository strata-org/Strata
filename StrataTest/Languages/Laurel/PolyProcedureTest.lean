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
meta import all StrataTest.Util.LaurelCorpusHarness

/-!
# Polymorphic procedure tests

Polymorphic *procedures*: per-call-site type-var freshening (CallElim), monomorphization when a generic composite is materialized at a type var, and uncalled-proc witnesses.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-! ## Polymorphic procedures verify soundly (CallElim per-call-site freshening)

Polymorphic *procedures* route through TransparencyPass → `$asFunction` + CallElim
contract-inlining; CallElim renames the callee's type variables to globally-fresh
names at each call site (`freshenTypeArgsSubst`), so the same procedure can be
instantiated at different concrete types in one body without the shared variable
forcing every site to unify with one sort.

These tests pin: single-instantiation is sound (true assertion verifies, false one
fails), multi-instantiation in one body works, and a poison multi-instantiation
does not mask a sibling procedure's real bug. -/

/-- Identity procedure with `ensures y == x`, instantiated at int. The true
    assertion must verify; the false one must fail (soundness). -/
def polyProcSound := r"
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };
procedure useGood() opaque { var a: int := idp(5); assert a == 5 };
procedure useBad() opaque { var b: int := idp(5); assert b == 6 };"

/-- Same procedure instantiated at TWO different types in ONE body — per-call-site
    freshening keeps the two sites' type variables independent. Must verify. -/
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

private def outerInner := r"
composite Box<T> { var val: T }
procedure inner<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure outer<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := inner(b) };
"

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
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 7 && gb == true };"},

  { name := "poly_proc_freshen_crossslot_wrong_int", outcome := .failsExactly 1,
    why := "a wrong INT result must FAIL (one slot) — freshening soundness"
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 8 && gb == true };"},

  { name := "poly_proc_freshen_crossslot_wrong_bool", outcome := .failsExactly 1,
    why := "a wrong BOOL result must FAIL (the other slot) — freshening soundness"
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 7 && gb == false };"},
  -- Procedure monomorphization for a generic-composite param `f<T>(b: Box<T>)`: clone +
  -- substTypeVars per call-site inst, ids cleared so clones re-resolve independently. KEYSTONE
  -- is reading the boxed field `b#val` off the monomorph (param-passing alone passed for an
  -- adjacent reason without exercising field use).
  { name := "poly_proc_generic_composite_param", outcome := .verifies,
    why := "`unbox<T>(b: Box<T>)` reading `b#val` at int verifies (procedure monomorphization)"
    src := r"
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := unbox(bx); assert got == 7 };"},

  { name := "poly_proc_generic_composite_param_wrong", outcome := .failsExactly 1,
    why := "reading `b#val`==7 then asserting got==8 must FAIL — the field read is real, not havoc'd"
    src := r"
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := unbox(bx); assert got == 8 };"},
  -- multi-inst reading fields: `unbox` at int AND bool, each reading ITS monomorph's field
  -- (clone id-clearing is load-bearing; without it the bodies cross-link).
  { name := "poly_proc_generic_composite_param_multi", outcome := .verifies,
    why := "`unbox<T>` reading fields at int AND bool both verify (no clone cross-link)"
    src := r"
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure u() opaque { var bi: Box<int> := new Box<int>; bi#val := 7; var gi: int := unbox(bi); var bb: Box<bool> := new Box<bool>; bb#val := true; var gb: bool := unbox(bb); assert gi == 7 && gb == true };"},

  { name := "poly_proc_generic_composite_param_multi_wrong", outcome := .failsExactly 1,
    why := "a wrong bool read across int+bool monomorphs must FAIL (int passing must not mask bool)"
    src := r"
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure u() opaque { var bi: Box<int> := new Box<int>; bi#val := 7; var gi: int := unbox(bi); var bb: Box<bool> := new Box<bool>; bb#val := true; var gb: bool := unbox(bb); assert gi == 7 && gb == false };"},

  { name := "poly_proc_generic_composite_param_false_post", outcome := .failsExactly 1,
    why := "a FALSE postcondition on a Box<T>-param proc must FAIL — monomorphized contract is sound, not vacuous"
    src := r"
composite Box<T> { var val: T }
procedure pk<T>(b: Box<T>) returns (r: int) opaque ensures r == 0 { r := 1 };
procedure u() opaque { var bx: Box<int> := new Box<int>; var g: int := pk(bx); assert 1 == 1 };"},

  { name := "poly_proc_generic_composite_param_precond_wrong", outcome := .failsExactly 2,
    why := "a violated precondition on the generic field `b#val` must GATE — requires-clauses monomorphize + are checked; exactly 2 fail (the precondition VC + the caller's `assert got==7`, unprovable once the bad call havocs `got`)"
    src := r"
composite Box<T> { var val: T }
procedure get7<T>(b: Box<T>) returns (r: T) requires b#val == 7 opaque ensures r == b#val { r := b#val };
procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 5; var got: int := get7(bx); assert got == 7 };"},

  { name := "poly_proc_concrete_composite_param", outcome := .verifies,
    why := "a CONCRETE `Box<int>` param is actually PASSED (take(x)) and its field observed via ensures — pins arg-passing, not just declaration"
    src := r"
composite Box<T> { var val: T }
procedure take(b: Box<int>) returns (r: int) opaque ensures r == b#val { r := b#val };
procedure u() opaque { var x: Box<int> := new Box; x#val := 7; var got: int := take(x); assert got == 7 };"},

  { name := "poly_proc_concrete_composite_param_wrong", outcome := .failsExactly 1,
    why := "a FALSE read of the passed `Box<int>`'s field must FAIL — concrete-composite arg passing is sound, not vacuous"
    src := r"
composite Box<T> { var val: T }
procedure take(b: Box<int>) returns (r: int) opaque ensures r == b#val { r := b#val };
procedure u() opaque { var x: Box<int> := new Box; x#val := 7; var got: int := take(x); assert got == 8 };"},
  -- #1121 coexistence — REJECT side. The `.TVar`-aware consistency arms (tvarize at
  -- registration; recursive `.Applied` arm; bare-name~instantiation arm) must NOT weaken the
  -- checker. Each of these is a type-incorrect program that must still be REJECTED; a leak
  -- here = the consistency relation was over-relaxed (and every accept-side test would stay green).
  { name := "tc_baseline_int_eq_true", outcome := .rejected (some .UserError),
    why := "#1121's non-poly checking untouched: `var x: int := true` rejects"
    src := r"procedure u() opaque { var x: int := true; assert 1 == 1 };"},
  { name := "tc_baseline_cross_composite", outcome := .rejected (some .UserError),
    why := "`var x: Dog := new Cat` (cross-composite) rejects"
    src := r"
composite Dog { var a: int }
composite Cat { var b: int }
procedure u() opaque { var x: Dog := new Cat; assert 1 == 1 };"},

  { name := "tc_boxint_to_boxbool", outcome := .rejected (some .UserError),
    why := "the recursive `.Applied` arm keeps strictness: `Box<int>` is NOT consistent with `Box<bool>`"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var a: Box<int> := new Box<int>; var b: Box<bool> := a; assert 1 == 1 };"},

  { name := "tc_boxint_arg_to_boolparam", outcome := .rejected (some .UserError),
    why := "passing `Box<int>` to a `Box<bool>` param rejects"
    src := r"
composite Box<T> { var val: T }
procedure needsBool(b: Box<bool>) opaque { assert 1 == 1 };
procedure u() opaque { var a: Box<int> := new Box<int>; needsBool(a); assert 1 == 1 };"},

  { name := "tc_barename_wrong_base", outcome := .rejected (some .UserError),
    why := "the bare-name~instantiation arm fires only on matching bases: bare `new Dog` into `Box<int>` rejects"
    src := r"
composite Box<T> { var val: T }
composite Dog { var a: int }
procedure u() opaque { var b: Box<int> := new Dog; assert 1 == 1 };"},

  { name := "tc_tvarbody_int_eq_true", outcome := .rejected (some .UserError),
    why := "the `.TVar` wildcard must not blanket-disable checking inside a poly body: `var y: int := true` still rejects"
    src := r"procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { var y: int := true; r := x };"},
  { name := "tc_polyfn_return_type_mismatch", outcome := .rejected (some .UserError),
    why := "an ill-typed poly FUNCTION (`coerce<A,B>(x: A): B { x }` returns an `A` where `B` is required) is rejected — the Core type error is RETURNED as a diagnostic, not thrown (translated=false)"
    src := r"
function coerce<A, B>(x: A): B { x };
procedure u() opaque { assert 1 == 1 };"},
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
  { name := "poly_proc_chain_divergent", outcome := .rejectedExactly .NotYetImplemented,
    why := "an unbounded proc chain (`grow<T>` deepening via `Box<Box<T>>`) must FAIL LOUD via the depth cap with ONLY `.NotYetImplemented` — no `.StrataBug` cascade folded on top (the re-resolution net must suppress the dangling-monomorph internal error once the depth cap already rejected)"
    src := r"
composite Box<T> { var val: T }
procedure grow<T>(b: Box<T>) returns (r: T) opaque ensures true { var bb: Box<Box<T>> := new Box<Box<T>>; var x: Box<T> := grow(bb); r := b#val };
procedure u() opaque { var bx: Box<int> := new Box<int>; var got: int := grow(bx); assert 1 == 1 };"},
  -- BODY-SCAN trigger: a value-`T`-signature proc that materializes a generic composite in
  -- its BODY (`var t: Box<T> := new Box<T>`) must MONOMORPHIZE, not ride freshening (which
  -- has no Core representation for a generic composite → body-local box's write would survive
  -- un-lowered → StrataBug). Found by an adversarial probe.
  { name := "poly_proc_body_local_generic_box", outcome := .verifies,
    why := "a value-T proc allocating a `Box<T>` in its BODY monomorphizes + verifies (body-scan trigger)"
    src := r"
composite Box<T> { var val: T }
procedure mkl<T>(x: T) returns (r: T) opaque ensures r == x { var t: Box<T> := new Box<T>; t#val := x; r := t#val };
procedure u() opaque { var got: int := mkl(7); assert got == 7 };"},

  { name := "poly_proc_body_local_generic_box_wrong", outcome := .failsExactly 1,
    why := "a wrong value from the body-local-box proc must FAIL — sound, not vacuous"
    src := r"
composite Box<T> { var val: T }
procedure mkl<T>(x: T) returns (r: T) opaque ensures r == x { var t: Box<T> := new Box<T>; t#val := x; r := t#val };
procedure u() opaque { var got: int := mkl(7); assert got == 8 };"},

  { name := "poly_proc_value_t_still_freshens", outcome := .verifies,
    why := "HYBRID PARTITION: a value-T proc touching NO generic composite still rides freshening (body-scan must not over-capture) — int AND bool"
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 7 && gb == true };"},
  -- An UNCALLED value-`T` poly proc (kept verbatim, NOT witness-cloned — it touches no generic
  -- composite) still has its own body VC emitted + discharged: a TRUE postcondition verifies,
  -- a FALSE one fails loud. Pins that the uncalled value-`T` path is never silently unchecked.
  { name := "poly_proc_value_t_uncalled_true", outcome := .verifies,
    why := "an uncalled value-T poly proc with a TRUE postcondition (`ensures r==x`) verifies — its body VC is checked even with no call site"
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { assert 1 == 1 };"},

  { name := "poly_proc_value_t_uncalled_false", outcome := .failsExactly 1,
    why := "an uncalled value-T poly proc with a FALSE postcondition (`ensures r==z` but `r:=x`) must FAIL — uncalled value-T contracts are not silently unchecked"
    src := r"
procedure bad<T>(x: T, z: T) returns (r: T) opaque ensures r == z { r := x };
procedure u() opaque { assert 1 == 1 };"},
  -- Synthetic WITNESS for uncalled composite-`T` procs: an uncalled proc would be dropped at
  -- emission (0 call sites → 0 clones), leaving its contract unchecked; we clone it at a
  -- fresh opaque zero-field composite per typevar so the contract is checked at a maximally-
  -- uninterpreted stand-in.
  { name := "poly_proc_uncalled_witness_false", outcome := .failsExactly 1,
    why := "a FALSE postcondition on an UNCALLED composite-T poly proc must FAIL at the witness (was silently 0 before)"
    src := r"
composite Box<T> { var val: T }
procedure bad<T>(b: Box<T>) returns (r: int) opaque ensures r == 0 { r := 1 };
procedure u() opaque { assert 1 == 1 };"},

  { name := "poly_proc_uncalled_witness_true", outcome := .verifies,
    why := "a TRUE contract on an uncalled poly proc must still VERIFY (the witness must not invent a false obligation)"
    src := r"
composite Box<T> { var val: T }
procedure good<T>(b: Box<T>) returns (r: int) opaque ensures r == 0 { r := 0 };
procedure u() opaque { assert 1 == 1 };"},

  { name := "poly_proc_uncalled_witness_field_false", outcome := .failsExactly 1,
    why := "an uncalled proc whose body reads the WRONG box (`r == b#val` from a fresh box) must FAIL at the witness"
    src := r"
composite Box<T> { var val: T }
procedure rd<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { var t: Box<T> := new Box<T>; r := t#val };
procedure u() opaque { assert 1 == 1 };"},

  { name := "poly_proc_called_and_uncalled_mixed", outcome := .failsExactly 1,
    why := "a CALLED proc (real inst, no witness) + an UNCALLED false-contract proc (witness, FAILS) — witness emitted iff uncalled, exactly 1 failure"
    src := r"
composite Box<T> { var val: T }
procedure used<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure unused<T>(b: Box<T>) returns (r: int) opaque ensures r == 5 { r := 6 };
procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := used(bx); assert got == 7 };"},

  { name := "poly_proc_uncalled_divergent_witness", outcome := .rejectedExactly .NotYetImplemented,
    why := "an UNCALLED divergent poly proc must FAIL LOUD via the depth cap on the witness/second-drain path, with ONLY `.NotYetImplemented` — no `.StrataBug` cascade folded on top"
    src := r"
composite Box<T> { var val: T }
procedure grow<T>(b: Box<T>) returns (r: T) opaque ensures true { var bb: Box<Box<T>> := new Box<Box<T>>; var x: Box<T> := grow(bb); r := b#val };
procedure u() opaque { assert 1 == 1 };"},
  -- THREE uncalled procs with DISTINCT false postconditions ⇒ EXACTLY 3 failures (witness
  -- obligations counted distinctly, not merged/dropped; harness keys on `index:label`).
  { name := "poly_proc_witness_obligations_counted", outcome := .failsExactly 3,
    why := "3 uncalled procs with distinct FALSE postconditions yield EXACTLY 3 failures (no merge/drop)"
    src := r"
composite Box<T> { var val: T }
procedure b1<T>(b: Box<T>) returns (r: int) opaque ensures r == 1 { r := 0 };
procedure b2<T>(b: Box<T>) returns (r: int) opaque ensures r == 2 { r := 0 };
procedure b3<T>(b: Box<T>) returns (r: int) opaque ensures r == 3 { r := 0 };
procedure u() opaque { assert 1 == 1 };"},
  -- WITNESS IS NOT A SINGLETON: `ensures a#val == b#val` is FALSE in general (two boxes hold
  -- independent values) → must FAIL. If the witness sort were a singleton it would hold
  -- vacuously and mask the bug; failing ⇒ the sort has arbitrary cardinality (faithful tyvar).
  { name := "poly_proc_witness_not_singleton", outcome := .failsExactly 1,
    why := "an uncalled `ensures a#val==b#val` (false in general) must FAIL at the witness (else the witness sort is a singleton)"
    src := r"
composite Box<T> { var val: T }
procedure f<T>(a: Box<T>, b: Box<T>) returns (r: int) opaque ensures a#val == b#val { r := 0 };
procedure u() opaque { assert 1 == 1 };"},
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
    src := r"
composite Box<T> { var val: T }
procedure g<T>(b: Box<T>) opaque { assert 1 == 1 };
procedure h(x: Box<int>)
  invokeOn g(x)
  opaque
{ assert 1 == 1 };"} ]

/-- Polymorphic procedures: freshening + monomorphization, abort-mask freedom, cross-slot
    coupling, witness-checked uncalled contracts, and #1121 reject-side coexistence. -/
def runPolyProcedureTests : IO Unit := checkCases polyProcedureCorpus

#guard_msgs (drop info, error) in
#eval runPolyProcedureTests

end Strata.Laurel
