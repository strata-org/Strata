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

private def polyProcSound := r"
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };
procedure useGood() opaque { var a: int := idp(5); assert a == 5 };
procedure useBad() opaque { var b: int := idp(5); assert b == 6 };"

private def polyProcMultiInst := r"
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };
procedure useTwo() opaque {
    var a: int := idp(5);
    assert a == 5;
    var b: bool := idp(true);
    assert b == true
};"

private def polyProcNoAbortMask := r"
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
private def polyProcFalseAmongMany := r"
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
private def polyProcPrecondGated := r"
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
private def polyProcedureCorpus : List Case := [
  { name := "poly_proc_sound", knownEncoderErrors := 1, outcome := .failsExactly 1,
    why := "single inst: true verifies, the false `assert b == 6` fails (sound + complete)"
    src := polyProcSound },
  { name := "poly_proc_multi", knownEncoderErrors := 1, outcome := .verifies,
    why := "multi-inst (idp(5)+idp(true) in one body) verifies — per-call-site freshening, no 'unify T with bool'"
    src := polyProcMultiInst },
  { name := "poly_proc_no_abort_mask", knownEncoderErrors := 1, outcome := .failsExactly 1,
    why := "a poison multi-inst must NOT abort whole-program checking and mask realBug's `assert 1==2` (the ship-blocker)"
    src := polyProcNoAbortMask },
  { name := "poly_proc_false_among_many", knownEncoderErrors := 1, outcome := .failsExactly 1,
    why := "false `assert c==99` on the 3rd inst still caught — freshening per-site postcondition non-vacuous, no drift"
    src := polyProcFalseAmongMany },
  { name := "poly_proc_precond_gated", knownEncoderErrors := 1, outcome := .failsExactly 1,
    why := "a freshened precondition (`x>0` violated by pos(-3,..)) still gates a bad call"
    src := polyProcPrecondGated },
  -- CROSS-SLOT freshening: `callElimCmd` applies the same fresh subst to input types, output
  -- types, and pre/post EXPRESSIONS. `ensures r==x` COUPLES input+output type at each call —
  -- if a slot freshened to a different inst, the coupled obligation would be ill-formed or
  -- vacuous (silently unsound, invisible to the typechecker AND the sorry-stubbed CallElim
  -- proof). Verified at int+bool together, with a must-fail twin on EACH slot. This is the
  -- execution guardrail for the freshening, which has no live correctness proof.
  { name := "poly_proc_freshen_crossslot", knownEncoderErrors := 1, outcome := .verifies,
    why := "`ensures r==x` coupling input+output type verifies at int AND bool (no cross-slot drift)"
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 7 && gb == true };"},

  { name := "poly_proc_freshen_crossslot_wrong_int", knownEncoderErrors := 1, outcome := .failsExactly 1,
    why := "a wrong INT result must FAIL (one slot) — freshening soundness"
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 8 && gb == true };"},

  { name := "poly_proc_freshen_crossslot_wrong_bool", knownEncoderErrors := 1, outcome := .failsExactly 1,
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

  -- A BARE uninitialized generic-composite local `var t: Box<T>;` in a cloned poly proc body:
  -- parses to `.Var (.Declare)`, NOT `.Assign [.Declare]`. `substTypeVarsInStmtNode` must
  -- substitute + id-clear it just like the initialized form — else `Box<T>` survives the clone
  -- un-lowered and crashes at Core (a `.strataBug`). Regression pin for that missing arm.
  { name := "poly_proc_bare_generic_declare", outcome := .verifies,
    why := "a bare `var t: Box<T>;` inside a cloned poly proc translates cleanly (type-var substituted in the .Var(.Declare) slot)"
    src := r"
composite Box<T> { var val: T }
procedure mk<T>(x: T) returns (r: int) opaque ensures r == 0 { var t: Box<T>; r := 0 };
procedure u() opaque { var z: int := mk(7); assert 1 == 1 };"},
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
  { name := "tc_baseline_int_eq_true", outcome := .rejected (some .userError),
    why := "#1121's non-poly checking untouched: `var x: int := true` rejects"
    src := r"procedure u() opaque { var x: int := true; assert 1 == 1 };"},
  { name := "tc_baseline_cross_composite", outcome := .rejected (some .userError),
    why := "`var x: Dog := new Cat` (cross-composite) rejects"
    src := r"
composite Dog { var a: int }
composite Cat { var b: int }
procedure u() opaque { var x: Dog := new Cat; assert 1 == 1 };"},

  { name := "tc_boxint_to_boxbool", outcome := .rejected (some .userError),
    why := "the recursive `.Applied` arm keeps strictness: `Box<int>` is NOT consistent with `Box<bool>`"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var a: Box<int> := new Box<int>; var b: Box<bool> := a; assert 1 == 1 };"},

  { name := "tc_boxint_arg_to_boolparam", outcome := .rejected (some .userError),
    why := "passing `Box<int>` to a `Box<bool>` param rejects"
    src := r"
composite Box<T> { var val: T }
procedure needsBool(b: Box<bool>) opaque { assert 1 == 1 };
procedure u() opaque { var a: Box<int> := new Box<int>; needsBool(a); assert 1 == 1 };"},

  { name := "tc_barename_wrong_base", outcome := .rejected (some .userError),
    why := "the bare-name~instantiation arm fires only on matching bases: bare `new Dog` into `Box<int>` rejects"
    src := r"
composite Box<T> { var val: T }
composite Dog { var a: int }
procedure u() opaque { var b: Box<int> := new Dog; assert 1 == 1 };"},

  { name := "tc_tvarbody_int_eq_true", outcome := .rejected (some .userError),
    why := "the `.TVar` wildcard must not blanket-disable checking inside a poly body: `var y: int := true` still rejects"
    src := r"procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { var y: int := true; r := x };"},
  { name := "tc_polyfn_return_type_mismatch", outcome := .rejected (some .userError),
    why := "an ill-typed poly FUNCTION (`coerce<A,B>(x: A): B { x }` returns an `A` where `B` is required) is rejected — the Core type error is RETURNED as a diagnostic, not thrown (translated=false)"
    src := r"
procedure coerce<A, B>(x: A): B { return x };
procedure u() opaque { assert 1 == 1 };"},
  -- proc↔composite FIXPOINT: a poly proc whose body calls another poly proc passing the
  -- generic-composite param (`outer<T>` calls `inner<T>`). The unified worklist clones
  -- `outer$int`, discovers the now-concrete `inner(b:Box<int>)` call, clones `inner$int`,
  -- rewrites. Both hops monomorphize before Core translation.
  { name := "poly_proc_chain_fixpoint", outcome := .verifies,
    why := "`outer<T>` calling `inner<T>` monomorphizes through the fixpoint and verifies"
    src := outerInner ++ "procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := outer(bx); assert got == 7 };" },
  { name := "poly_proc_chain_fixpoint_wrong", outcome := .failsExactly 1,
    why := "a wrong value through the two-hop chain must FAIL — the inner clone's contract is threaded end-to-end"
    src := outerInner ++ "procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 7; var got: int := outer(bx); assert got == 99 };" },
  { name := "poly_proc_chain_fixpoint_multi", outcome := .verifies,
    why := "the outer→inner chain at int AND bool each monomorphize independently through the fixpoint"
    src := outerInner ++ "procedure u() opaque { var bi: Box<int> := new Box<int>; bi#val := 7; var gi: int := outer(bi); var bb: Box<bool> := new Box<bool>; bb#val := true; var gb: bool := outer(bb); assert gi == 7 && gb == true };" },
  { name := "poly_proc_chain_divergent", outcome := .rejectedExactly .notYetImplemented,
    why := "an unbounded proc chain (`grow<T>` deepening via `Box<Box<T>>`) must FAIL LOUD via the depth cap with ONLY `.notYetImplemented` — no `.strataBug` cascade folded on top (the re-resolution net must suppress the dangling-monomorph internal error once the depth cap already rejected)"
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

  { name := "poly_proc_value_t_still_freshens", knownEncoderErrors := 1, outcome := .verifies,
    why := "HYBRID PARTITION: a value-T proc touching NO generic composite still rides freshening (body-scan must not over-capture) — int AND bool"
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { var gi: int := idp(7); var gb: bool := idp(true); assert gi == 7 && gb == true };"},
  -- An UNCALLED value-`T` poly proc (kept verbatim, NOT witness-cloned — it touches no generic
  -- composite) still has its own body VC emitted + discharged: a TRUE postcondition verifies,
  -- a FALSE one fails loud. Pins that the uncalled value-`T` path is never silently unchecked.
  -- TRANSITIONAL: as with the `forall_over_tvar` twin, only the `_true` half currently pins
  -- its property; the `_false` half's single failure is the encoding error, so it is
  -- `inertUntilEncoderFix` until the two Core SMT-encoder fixes land.
  { name := "poly_proc_value_t_uncalled_true", knownEncoderErrors := 1, outcome := .verifies,
    why := "an uncalled value-T poly proc with a TRUE postcondition (`ensures r==x`) verifies — its body VC is checked even with no call site"
    src := r"
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure u() opaque { assert 1 == 1 };"},

  { name := "poly_proc_value_t_uncalled_false", knownEncoderErrors := 1, inertUntilEncoderFix := true, outcome := .failsExactly 1,
    why := "an uncalled value-T poly proc with a FALSE postcondition (`ensures r==z` but `r:=x`) must FAIL — uncalled value-T contracts are not silently unchecked"
    src := r"
procedure bad<T>(x: T, z: T) returns (r: T) opaque ensures r == z { r := x };
procedure u() opaque { assert 1 == 1 };"},
  -- QUANTIFIED-OVER-T body VC: a value-`T` proc whose postcondition quantifies over its OWN
  -- type var (`ensures forall(y: T) => ...`). The bare `T` here is the quantifier BINDER's
  -- type, synthesized DURING SMT encoding (the quant arm's `LMonoTy.toSMTType T`, and the
  -- polymorphic helper `fnty` destructured in `toSMTOp`) — so it is NOT in the obligation
  -- term and is invisible to the obligation-level free-tyvar seed in
  -- `ProofObligation.toSMTTerms`; `LMonoTy.toSMTType` must declare it as a fresh arity-0
  -- uninterpreted sort. The twin pins BOTH encodability AND soundness: `forall(y:T)=>y==y`
  -- holds in every interpretation (verifies), while `forall(y:T)=>y==x` is falsifiable once
  -- |T| >= 2 (an uninterpreted sort is not forced to be a singleton) so it must FAIL.
  -- TRANSITIONAL: only the `_true` half currently pins its property. Without the two Core
  -- SMT-encoder fixes the `_false` half's single failure IS the encoding error rather than a
  -- countermodel, so it is `inertUntilEncoderFix` and pins only translatability. The
  -- soundness half of this twin re-asserts when those fixes land.
  { name := "poly_proc_forall_over_tvar_true", knownEncoderErrors := 1, outcome := .verifies,
    why := "`ensures forall(y:T) => y==y` (valid in every interpretation) must VERIFY — the bare-T quantifier binder encodes as a fresh uninterpreted sort"
    src := r"
procedure allEq<T>(x: T) returns (r: bool) opaque ensures forall(y: T) => (y == y) { r := true };
procedure u() opaque { var b: bool := allEq(5); assert 1 == 1 };"},

  { name := "poly_proc_forall_over_tvar_false", knownEncoderErrors := 1, inertUntilEncoderFix := true, outcome := .failsExactly 1,
    why := "`ensures forall(y:T) => y==x` (false at cardinality >= 2) must FAIL — the auto-declared tyvar sort has arbitrary cardinality, so a false-in-general quantified-over-T contract is not vacuously verified (soundness twin of the encodability fix)"
    src := r"
procedure allEqBad<T>(x: T) returns (r: bool) opaque ensures forall(y: T) => (y == x) { r := true };
procedure u() opaque { var b: bool := allEqBad(5); assert 1 == 1 };"},
  -- MULTI-INSTANTIATION of one quantified-over-T helper: the same `allEqM$post0` is
  -- referenced at its own poly self-check AND at `int` and `bool` call sites. The SMT
  -- pending-def dedup key is the full `UF` (id + arg/out SORTS), so the three
  -- reference-instances are three distinct entries, each body-encoded with its own
  -- `smt_ty_inst` (`resolveOnePendingFnDef`). A per-NAME body shared across
  -- instantiations would be ill-sorted at all but one of them (binder `T` vs the
  -- instantiated sort), which the harness's toolchain-error gate catches.
  -- Failure count is 1, not 2: the helper has ONE body self-check VC; call sites
  -- contribute assumptions, not obligations.
  -- TRANSITIONAL: without the two Core SMT-encoder fixes this VC cannot be encoded at all,
  -- so the single failure IS the encoding error and no countermodel is produced — the case
  -- is `inertUntilEncoderFix` and currently pins only translatability, NOT the
  -- no-sort-bleed property described above. It re-asserts when the encoder fixes land.
  { name := "poly_proc_forall_over_tvar_multi_inst", knownEncoderErrors := 1, inertUntilEncoderFix := true, outcome := .failsExactly 1,
    why := "one quantified-over-T helper instantiated at int AND bool: every reference-instance must encode cleanly (per-UF body encoding, no cross-instantiation sort bleed) and the self-check still fails via countermodel"
    src := r"
procedure allEqM<T>(x: T) returns (r: bool) opaque ensures forall(y: T) => (y == x) { r := true };
procedure u() opaque { var bi: bool := allEqM(5); var bb: bool := allEqM(true); assert 1 == 1 };"},
  -- Synthetic WITNESS for uncalled composite-`T` procs: an uncalled proc would be dropped at
  -- emission (0 call sites → 0 clones), leaving its contract unchecked; we clone it at a
  -- fresh opaque zero-field composite per typevar so the contract is checked at a maximally-
  -- uninterpreted stand-in.
  { name := "poly_proc_uncalled_witness_false", outcome := .failsExactly 1,
    why := "a FALSE postcondition on an UNCALLED composite-T poly proc must FAIL at the witness (the witness-clone path checks the contract at an uninterpreted stand-in)"
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

  { name := "poly_proc_uncalled_divergent_witness", outcome := .rejectedExactly .notYetImplemented,
    why := "an UNCALLED divergent poly proc must FAIL LOUD via the depth cap on the witness/second-drain path, with ONLY `.notYetImplemented` — no `.strataBug` cascade folded on top"
    src := r"
composite Box<T> { var val: T }
procedure grow<T>(b: Box<T>) returns (r: T) opaque ensures true { var bb: Box<Box<T>> := new Box<Box<T>>; var x: Box<T> := grow(bb); r := b#val };
procedure u() opaque { assert 1 == 1 };"},
  -- THREE uncalled procs with DISTINCT false postconditions ⇒ EXACTLY 3 failures (witness
  -- obligations counted distinctly, not merged/dropped; each has a distinct source location,
  -- so the assertion-merge keying keeps them separate).
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
{ assert 1 == 1 };"},

  -- ── Polymorphism × exceptions ──────────────────────────────────────────────
  -- A poly proc that ALSO `throws`, monomorphized at a concrete instantiation. The
  -- monomorphizer clones the proc (T in the `Box<T>` param) and EliminateExceptions lowers
  -- its `throws` to `Result<Val, Err>`. `cloneProcAt` must substitute the clone's exception
  -- contract (throwsType/throwsBinding/throwsOn) — else the clone keeps `.TVar T` and
  -- EliminateExceptions builds `Result<Val, T>` with a dangling type var.

  -- (a) throws a CONCRETE type: the baseline that always worked; pins it stays sound.
  { name := "poly_proc_throws_concrete", outcome := .verifies,
    why := "a poly proc throwing a CONCRETE type, monomorphized at int, verifies through the Result lowering"
    src := r"
composite Box<T> { var val: T }
composite E {}
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: E) opaque ensures r == b#val { r := b#val };
procedure u() returns (out: int) opaque {
  var bx: Box<int> := new Box<int>; bx#val := 7;
  try { out := unbox(bx); assert out == 7 } catch c { out := 0 }
};"},

  -- (b) throws the TYPE VARIABLE `T`: the clone's Result Err is the instantiation (int), not a
  -- dangling `.TVar T`, so the monomorphized `throws (e:T)` resolves at the concrete type.
  { name := "poly_proc_throws_tvar", outcome := .verifies,
    why := "a poly proc `throws (e:T)` monomorphized at int: cloneProcAt substitutes the throws type so the clone's Result carries the concrete Err (not a dangling `.TVar T`)"
    src := r"
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: T) opaque ensures r == b#val { r := b#val };
procedure u() returns (out: int) opaque {
  var bx: Box<int> := new Box<int>; bx#val := 7;
  try { out := unbox(bx); assert out == 7 } catch c { out := 0 }
};"},

  -- (b-false) the false twin of (b) must FAIL — proves the throws-tvar path is sound, not
  -- vacuously accepting.
  { name := "poly_proc_throws_tvar_false", outcome := .failsExactly 1,
    why := "the false twin of poly_proc_throws_tvar (assert out == 999 on the good path) must fail"
    src := r"
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: T) opaque ensures r == b#val { r := b#val };
procedure u() returns (out: int) opaque {
  var bx: Box<int> := new Box<int>; bx#val := 7;
  try { out := unbox(bx); assert out == 999 } catch c { out := 0 }
};"},

  -- (c) generic composite in the THROWS type only: `mentionsGenericComposite`/`collectSeeds`
  -- must scan `throwsType` so `Box<int>` is indexed + monomorphized; else `Box` survives
  -- un-lowered and re-resolution fails "'Box' is not defined".
  { name := "poly_proc_throws_generic_composite", outcome := .verifies,
    why := "a proc throwing a generic-composite instantiation (`throws Box<int>`) seeds + monomorphizes Box$a1$int via the throwsType scan"
    src := r"
composite Box<T> { var val: T }
procedure mayThrow(x: int) returns (r: int) throws (e: Box<int>) opaque ensures r == x { r := x };
procedure u() returns (out: int) opaque {
  try { out := mayThrow(3); assert out == 3 } catch c { out := 0 }
};"},

  -- (d) poly `throws (e:T)` that flows UNCAUGHT through a caller declaring a compatible
  -- `throws`. Exercises the escape path (no catch-all wrapper), which the (a)–(c) cases —
  -- all wrapped in `try{…}catch{…}` — do NOT. At the initial resolution the callee's throws
  -- is `.TVar T`, deferred by `exceptionEscapes` (`mentionsTVar`); post-mono the clone
  -- throws `int` and the caller also declares `throws int`, so `isSubtype int int` holds and
  -- the escape re-check (un-gated `validateExceptionEscapes`) passes.
  { name := "poly_proc_throws_escape_ok", outcome := .verifies,
    why := "an uncaught poly `throws (e:T)`@int escaping into a `throws int` caller is accepted: deferred at initial resolve, re-checked concretely post-mono"
    src := r"
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: T) opaque ensures r == b#val { r := b#val };
procedure caller(b: Box<int>) returns (r: int) throws (e: int) opaque ensures r == b#val { r := unbox(b) };
procedure u() returns (out: int) opaque {
  var bx: Box<int> := new Box<int>; bx#val := 7;
  try { out := caller(bx); assert out == 7 } catch c { out := 0 }
};"},

  -- (d-mismatch) THE SOUNDNESS GUARD. Same shape as (d) but the caller declares `throws bool`
  -- while the callee throws `T`@int. At the initial resolve the `.TVar T` is deferred (so this
  -- is NOT rejected pre-mono, the old false-positive); post-mono the clone throws `int`, and the
  -- un-gated escape re-check fires `int </: bool`. The mismatch surfaces at the post-mono
  -- re-resolution as a NEW `.userError`, which the pipeline's `isExceptionContract` exemption
  -- passes through UNCHANGED (not wrapped as `.strataBug`). `.rejectedExactly .userError` pins
  -- BOTH invariants at once: soundness (the program is rejected — the escape guard is not a
  -- no-op for poly throws) AND diagnostic quality (a clean user error, no internal-error net).
  -- If Site 1's deferral regresses this rejects pre-mono; if Site 3's exemption wording drifts
  -- the kind flips to `.strataBug` and this fails loud — the intended tripwire.
  { name := "poly_proc_throws_escape_mismatch", outcome := .rejectedExactly .userError,
    why := "an uncaught poly `throws (e:T)`@int escaping into a `throws bool` caller is rejected post-mono as a clean userError (int is not a subtype of bool); guards the soundness backstop + the strataBug exemption"
    src := r"
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: T) opaque ensures r == b#val { r := b#val };
procedure caller(b: Box<int>) returns (r: int) throws (e: bool) opaque ensures r == b#val { r := unbox(b) };
procedure u() returns (out: int) opaque {
  var bx: Box<int> := new Box<int>; bx#val := 7;
  try { out := caller(bx); assert out == 7 } catch c { out := 0 }
};"},

  -- (e) poly `throws Box<T>` (a type MENTIONING a type var, not a bare `.TVar`). Verifies
  -- Site 1's generalization beyond bare type vars: `mentionsTVar` must recurse into the
  -- `.Applied` so the escape is deferred at the initial resolve, exactly as a poly return
  -- flows through `isConsistent`'s recursive `.Applied` wildcard arm. A bare-`.TVar`-only
  -- drop would spuriously reject this pre-mono with "'T' is not defined".
  { name := "poly_proc_throws_applied_tvar_escape_ok", outcome := .verifies,
    why := "an uncaught poly `throws Box<T>`@int escaping into a `throws Box<int>` caller is accepted: mentionsTVar recurses into the .Applied to defer it at initial resolve"
    src := r"
composite Box<T> { var val: T }
procedure mayThrow<T>(b: Box<T>) returns (r: T) throws (e: Box<T>) opaque ensures r == b#val { r := b#val };
procedure caller(b: Box<int>) returns (r: int) throws (e: Box<int>) opaque ensures r == b#val { r := mayThrow(b) };
procedure u() returns (out: int) opaque {
  var bx: Box<int> := new Box<int>; bx#val := 7;
  try { out := caller(bx); assert out == 7 } catch c { out := 0 }
};"} ]

/-- Polymorphic procedures: freshening + monomorphization, abort-mask freedom, cross-slot
    coupling, witness-checked uncalled contracts, and #1121 reject-side coexistence. -/
private def runPolyProcedureTests : IO Unit := checkCases polyProcedureCorpus

#guard_msgs (drop info, error) in
#eval runPolyProcedureTests

end Strata.Laurel
