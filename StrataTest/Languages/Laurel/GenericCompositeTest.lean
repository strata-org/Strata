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
# Generic composite tests

Generic composites end-to-end: monomorphization, nested generics, Map-typed fields, `new C<τ>`, chained writes, `is`/`as`, and type aliases.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

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
  -- `Box<Map int int>`: a generic composite instantiated at a COLLECTION type. Since
  -- `instTagCommon` now tags `.TMap` (`Map$a2$int$int`), this monomorphizes and verifies
  -- (previously an un-taggable fail-loud limitation). SOUND, not coalescing — the
  -- `map_fields_distinct` twin below pins that distinct `(K,V)` Map fields stay distinct
  -- boxes, and the `*_wrong` cases pin that false reads fail.
  { name := "generic_box_map_arg", outcome := .verifies,
    why := "`Box<Map int int>` monomorphizes via the `.TMap` tag; field round-trips"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var b: Box<Map int int> := new Box<Map int int>; b#val := update(b#val, 1, 2); assert select(b#val, 1) == 2 };"},

  { name := "generic_box_map_arg_wrong", outcome := .failsExactly 1,
    why := "a FALSE read of the boxed `Map int int` field must FAIL — the Map-tag boxing is sound, not vacuous"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var b: Box<Map int int> := new Box<Map int int>; b#val := update(b#val, 1, 2); assert select(b#val, 1) == 3 };"},
  -- Item 1: READING/WRITING a `Map`-typed COMPOSITE FIELD heap-boxes via the `.TMap`
  -- instTagCommon arm (previously `boxDestructorNameError`, fail-loud). Sound: false read fails.
  { name := "map_field_read", outcome := .verifies,
    why := "read/write a `Map`-typed composite field round-trips (heap-boxed via the `.TMap` tag)"
    src := r"
composite H { var m: Map int bool }
procedure u() opaque { var h: H := new H; h#m := update(h#m, 3, true); assert select(h#m, 3) == true };"},

  { name := "map_field_read_wrong", outcome := .failsExactly 1,
    why := "a FALSE read of the Map-typed field must FAIL — the field boxing is sound, not vacuous"
    src := r"
composite H { var m: Map int bool }
procedure u() opaque { var h: H := new H; h#m := update(h#m, 3, true); assert select(h#m, 3) == false };"},

  { name := "map_fields_distinct", outcome := .verifies,
    why := "two DIFFERENT-(K,V) Map fields in one composite both round-trip — distinct instantiations stay distinct boxes (no coalescing)"
    src := r"
composite H { var mib: Map int bool
  var mii: Map int int }
procedure u() opaque { var h: H := new H; h#mib := update(h#mib, 1, true); h#mii := update(h#mii, 1, 9); assert select(h#mib, 1) == true; assert select(h#mii, 1) == 9 };"},

  { name := "map_fields_distinct_wrong", outcome := .failsExactly 1,
    why := "a FALSE read of the second distinct Map field (mii) must FAIL — the per-(K,V) boxes are sound, not vacuous (non-coalescing itself is pinned by the verifying `map_fields_distinct` twin)"
    src := r"
composite H { var mib: Map int bool
  var mii: Map int int }
procedure u() opaque { var h: H := new H; h#mib := update(h#mib, 1, true); h#mii := update(h#mii, 1, 9); assert select(h#mii, 1) == 8 };"},
  -- A generic over a COLLECTION type (`Map K V`): the consistency relation recurses into
  -- `.TMap` element-wise (like `.Applied`) so a concrete `Map int bool` argument satisfies a
  -- `Map K V` parameter — the nested `int`/`bool` reach the `.TVar` wildcard. Without the
  -- `.TMap` consistency arm this was spuriously over-rejected ("expected 'Map K V', got
  -- 'Map int bool'"). The `ensures r == m` makes the accept OBSERVABLE (a real obligation),
  -- not just translatable; the strictness twin pins that concrete-vs-concrete stays strict.
  { name := "generic_map_param", outcome := .verifies,
    why := "a concrete `Map int bool` into a generic `Map K V` proc param verifies, returned map observed via `ensures r == m`"
    src := r"
procedure idm<K,V>(m: Map K V) returns (r: Map K V) opaque ensures r == m { r := m };
procedure u() opaque { var mm: Map int bool; var rr: Map int bool := idm(mm); assert rr == mm };"},

  { name := "generic_map_param_wrong", outcome := .failsExactly 1,
    why := "the returned map equals `mm`, not the unrelated `nn` — `assert rr == nn` must FAIL (accept is sound, not vacuous)"
    src := r"
procedure idm<K,V>(m: Map K V) returns (r: Map K V) opaque ensures r == m { r := m };
procedure u() opaque { var mm: Map int bool; var nn: Map int bool; var rr: Map int bool := idm(mm); assert rr == nn };"},

  { name := "map_concrete_mismatch", outcome := .rejected,
    why := "STRICTNESS: a concrete `Map int int` into a `Map int bool` param must be REJECTED — the `.TMap` arm recurses but stays strict on concrete leaves (no hole opened)"
    src := r"
procedure needsIB(m: Map int bool) opaque { assert 1 == 1 };
procedure u() opaque { var mm: Map int int; needsIB(mm); assert 1 == 1 };"},
  -- Generic-composite instantiation in type positions beyond the original three (field /
  -- proc in-out / body Declare); the monomorphizer now collects+rewrites every position.
  { name := "generic_in_datatype", outcome := .verifies,
    why := "Box<int> as a datatype ctor arg is collected + rewritten"
    src := r"
composite Box<T> { var val: T }
datatype Wrap { MkWrap(b: Box<int>) }
procedure u() opaque { assert 1 == 1 };"},

  { name := "generic_in_quant", outcome := .verifies,
    why := "forall over a Box<int> binder translates"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var p: bool := forall(b: Box<int>) => true; assert p };"},

  { name := "generic_in_quant_wrong", outcome := .failsExactly 1,
    why := "a FALSE quantified claim over a Box<int> binder must FAIL — sound, not vacuous"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var p: bool := forall(b: Box<int>) => false; assert p };"},
  -- A standalone declaration WITHOUT an initializer (`var b: Box<int>;`) parses to
  -- `.Var (.Declare …)`, NOT the `.Assign [.Declare …] e` form — a distinct statement-type
  -- slot the monomorphizer's `stmtTypeSlots`/`rewriteStmt` must also cover, else `Box<int>`
  -- survives un-lowered to Core.
  { name := "generic_decl_no_init", outcome := .verifies,
    why := "a no-initializer generic decl `var b: Box<int>;` must lower (be collected + rewritten), not survive un-lowered to Core"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var b: Box<int>; assert 1 == 1 };"},
  -- A generic instantiation in a CONTRACT (precondition quantifier binder), not the body —
  -- the monomorphizer's collect + final rewrite must reach precondition/decreases/invokeOn
  -- positions, not only procedure bodies.
  { name := "generic_in_precondition", outcome := .verifies,
    why := "`Box<int>` in a precondition quantifier binder must be collected + rewritten (contract positions, not just body)"
    src := r"
composite Box<T> { var val: T }
procedure u()
  requires forall(b: Box<int>) => true
  opaque
{ assert 1 == 1 };"},
  -- Field SELECT inside a quantifier BODY (a triggerless quantifier's body was skipped by
  -- heap-read analysis — a do-block sequencing bug — so `c#v` survived to fail at translation).
  { name := "quant_body_field", outcome := .verifies,
    why := "a TRUE field-read fact in a quantifier body verifies (heap-read-in-body fix)"
    src := r"
composite C { var v: int }
procedure u() opaque { var p: bool := forall(c: C) => c#v == c#v; assert p };"},

  { name := "quant_body_field_wrong", outcome := .failsExactly 1,
    why := "a FALSE field-read fact in a quantifier body must FAIL — sound, not vacuous"
    src := r"
composite C { var v: int }
procedure u() opaque { var p: bool := forall(c: C) => c#v == 5; assert p };"},

  { name := "generic_box_map_in_datatype", outcome := .verifies,
    why := "`Box<Map int int>` as a datatype ctor arg monomorphizes via the `.TMap` tag in this position too (was un-taggable fail-loud); construction round-trips by equality"
    src := r"
composite Box<T> { var val: T }
datatype Wrap { MkWrap(b: Box<Map int int>) }
procedure u() opaque { var b: Box<Map int int> := new Box<Map int int>; var w: Wrap := MkWrap(b); assert w == MkWrap(b) };"},
  -- NESTED GENERICS: a composite whose field is a generic instantiation of the same param
  -- (`Pair<T> { b: Box<T> }`). (A) sound when the inner inst is also named directly.
  { name := "nested_generic", outcome := .verifies,
    why := "Pair<int> with field Box<int> (Box<int> also named) resolves + verifies"
    src := r"
composite Box<T> { var val: T }
composite Pair<T> { var b: Box<T> }
procedure u() opaque { var inner: Box<int> := new Box; inner#val := 5; var p: Pair<int> := new Pair; p#b := inner; var got: Box<int> := p#b; assert got#val == 5 };"},

  { name := "nested_generic_wrong", outcome := .failsExactly 1,
    why := "a FALSE read of the nested field must FAIL — sound, not vacuous"
    src := r"
composite Box<T> { var val: T }
composite Pair<T> { var b: Box<T> }
procedure u() opaque { var inner: Box<int> := new Box; inner#val := 5; var p: Pair<int> := new Pair; p#b := inner; var got: Box<int> := p#b; assert got#val == 6 };"},
  -- (B) the fixpoint worklist: inner inst reachable ONLY through the outer's substituted
  -- field (`q#b := p#b`, Box<int> named nowhere else) is now discovered + emitted.
  { name := "nested_generic_via_field_only", outcome := .verifies,
    why := "`q#b := p#b` (inner Box<int> reachable only via the field) translates (fixpoint worklist)"
    src := r"
composite Box<T> { var val: T }
composite Pair<T> { var b: Box<T> }
procedure u() opaque { var p: Pair<int> := new Pair; var q: Pair<int> := new Pair; q#b := p#b; assert 1 == 1 };"},

  { name := "nested_generic_via_field_wrong", outcome := .failsExactly 1,
    why := "a FALSE read of the field-only-reachable nested monomorph must FAIL — sound, not vacuous"
    src := r"
composite Box<T> { var val: T }
composite Pair<T> { var b: Box<T> }
procedure u() opaque { var p: Pair<int> := new Pair; var inner: Box<int> := new Box; inner#val := 7; p#b := inner; var got: Box<int> := p#b; assert got#val == 8 };"},
  -- TERMINATION + clean rejection: a divergent recursive generic (`L<T>{ next: L<L<T>> }`)
  -- is cut off at the depth bound and rejected LOUD — not a hang, not dead monomorphs.
  { name := "recursive_generic_rejected", outcome := .rejected (some .NotYetImplemented),
    why := "divergent `L<L<T>>` must be REJECTED via the depth-cap NotYetImplemented diagnostic (the test completing proves termination)"
    src := r"
composite L<T> { var next: L<L<T>> }
procedure u() opaque { var x: L<int> := new L; assert 1 == 1 };"},
  -- EXPLICIT `new C<τ>` SYNTAX: allocation carries its instantiation, so it works in every
  -- position incl. field-write + call-arg (which previously crashed in Core on `C_TypeTag`).
  { name := "new_typeargs_field", outcome := .verifies,
    why := "`new Box<int>` in a field-write context verifies (was a Box_TypeTag crash)"
    src := r"
composite Box<T> { var val: T }
composite Holder { var b: Box<int> }
procedure u() opaque { var h: Holder := new Holder; var inner: Box<int> := new Box<int>; inner#val := 7; h#b := inner; var got: Box<int> := h#b; assert got#val == 7 };"},

  { name := "new_typeargs_field_wrong", outcome := .failsExactly 1,
    why := "a FALSE read after `new Box<int>` field write must FAIL"
    src := r"
composite Box<T> { var val: T }
composite Holder { var b: Box<int> }
procedure u() opaque { var h: Holder := new Holder; var inner: Box<int> := new Box<int>; inner#val := 7; h#b := inner; var got: Box<int> := h#b; assert got#val == 8 };"},

  { name := "new_typeargs_arg", outcome := .verifies,
    why := "`new Box<int>` as a call argument verifies (also previously crashed)"
    src := r"
composite Box<T> { var val: T }
procedure take(x: Box<int>) opaque { assert 1 == 1 };
procedure u() opaque { take(new Box<int>); assert 1 == 1 };"},

  { name := "new_typeargs_two_inst", outcome := .verifies,
    why := "two explicit `new Box<τ>` instantiations pick DISTINCT monomorphs (no coalescing)"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var a: Box<int> := new Box<int>; a#val := 5; var b: Box<bool> := new Box<bool>; b#val := true; assert a#val == 5 };"},
  -- ARITY: an explicit `new C<τ…>` must supply exactly the composite's declared type-arg
  -- count. Surplus args would otherwise be silently dropped by the monomorphizer's `zip`.
  { name := "new_typeargs_wrong_arity", outcome := .rejected (some .UserError),
    why := "`new Box<int,bool>` for a single-param `Box<T>` must be REJECTED with a clean UserError (type-arg arity check), not the StrataBug net"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var b: Box<int, bool> := new Box<int, bool>; b#val := 7; assert b#val == 7 };"},

  { name := "new_bare_legacy", outcome := .verifies,
    why := "bare `new Box` in the legacy `var x: C<τ> := new C` form still works (args from declared type)"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box; b#val := 1; assert b#val == 1 };"},
  -- SELF-SEEDING: `new Box<bool>` is the SOLE mention of Box<bool> (generic sink, no type
  -- annotation seeds it) — the monomorph must be collected from the allocation site itself.
  { name := "new_typeargs_self_seed", outcome := .verifies,
    why := "`new Box<bool>` as the sole mention (via a generic sink) is collected + verifies (collect/rewrite agree)"
    src := r"
composite Box<T> { var val: T }
function sink<T>(x: T): int { 0 };
procedure u() opaque { var r: int := sink(new Box<bool>); assert r == 0 };"},
  -- CHAINED field WRITE `o#i#v := …` via the dedicated `FieldPath` grammar category (a
  -- separate category from `StmtExpr` so it can't collide with a `multiAssign` value).
  { name := "chained_field_write", outcome := .verifies,
    why := "`o#i#v := 5` then read verifies (chained-write via FieldPath)"
    src := r"
composite Inner { var v: int }
composite Outer { var i: Inner }
procedure u() opaque { var o: Outer := new Outer; var x: Inner := new Inner; o#i := x; o#i#v := 5; assert o#i#v == 5 };"},

  { name := "chained_field_write_wrong", outcome := .failsExactly 1,
    why := "a FALSE read after `o#i#v := 5` must FAIL — chained write is sound, not vacuous"
    src := r"
composite Inner { var v: int }
composite Outer { var i: Inner }
procedure u() opaque { var o: Outer := new Outer; var x: Inner := new Inner; o#i := x; o#i#v := 5; assert o#i#v == 6 };"},
  -- Item-5 guard: a heap-writer with a USER output named `$heap` must FAIL LOUD (never translate),
  -- because HeapParameterization prepends a synth `$heap` inout to a writer's inputs AND outputs.
  -- The re-resolution fold type-checks the user `$heap` against the synth `$heap: Heap` and fails
  -- loud (`expected 'Heap', got 'int'`, or `Duplicate definition '$heap'` via the seen-outputs
  -- dup-check) — either way `!translated`. This pins only "a user `$heap` output never translates";
  -- the sanity twin pins that the legit single synth `$heap` inout still merges.
  { name := "user_heap_output_rejected", outcome := .rejected (some .StrataBug),
    why := "a user output named `$heap` on a heap-writer collides with the synth heap inout and must never translate; rejects via the re-resolution internal-error net (.StrataBug — `Duplicate definition '$heap'` and/or the `expected 'Heap', got 'int'` type-mismatch). The .StrataBug tag pins that it rejects via that net, NOT which specific diagnostic (the dup-check's effect is cosmetic — cleaner message — not separately machine-checked here)"
    src := r"
composite Inner { var v: int }
procedure u() returns ($heap: int) opaque { var o: Inner := new Inner; o#v := 5; $heap := 0 };"},

  { name := "ordinary_heap_writer_verifies", outcome := .verifies,
    why := "the same heap-writer WITHOUT a user `$heap` output still verifies (the single synth `$heap` inout merge must not regress)"
    src := r"
composite Inner { var v: int }
procedure u() opaque { var o: Inner := new Inner; o#v := 5; assert o#v == 5 };"},
  -- Regression guard: a `multiAssign` value may be a CALL (`assign t := f()`); the FieldPath
  -- category must NOT compete with it (an `obj: StmtExpr` form mis-parsed `f()` as a field obj).
  { name := "multiassign_call_value", outcome := .verifies,
    why := "`assign var x, var y := two()` parses + translates (FieldPath must not collide with the value)"
    src := r"
procedure two() returns (a: int, b: int) opaque ensures a == 1 ensures b == 2 { a := 1; b := 2 };
procedure u() opaque { assign var x: int, var y: int := two(); assert x == 1 };"},
  -- 7(B): `is`/`as` operands are now a full `LaurelType` (was a bare `Ident`), so a generic
  -- instantiation can be the test/cast target. Baseline (monomorphic) first, then generic.
  { name := "is_monomorphic_baseline", outcome := .verifies,
    why := "`p is Plain` against a monomorphic composite verifies (the non-generic baseline)"
    src := r"
composite Plain { var v: int }
procedure u() opaque { var p: Plain := new Plain; assert p is Plain };"},

  { name := "is_generic_inst", outcome := .verifies,
    why := "`b is Box<int>` (specific instantiation) verifies — operand monomorphizes to `Box$a1$int`, lowerIsType keys its `_TypeTag`"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; assert b is Box<int> };"},

  { name := "is_generic_wrong_inst", outcome := .rejected (some .UserError),
    why := "`Box<int> is Box<bool>` — distinct instantiations are unrelated, rejected with a clean UserError (sound, no crash)"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; assert b is Box<bool> };"},

  { name := "as_generic_inst", outcome := .verifies,
    why := "`b as Box<int>` (downcast to the matching instantiation) verifies — `as` lowers via the HeapParam is-guard"
    src := r"
composite Box<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; var c: Box<int> := b as Box<int>; assert c#val == c#val };"},
  -- 7(C): type-alias surface form `type Name = Target`. Backend (`TypeAliasElim`) was wired;
  -- this exercises the new grammar/parse + the `resolveFieldInTypeScope` alias-unfold for
  -- composite-typed aliases. NOTE: no trailing `;` after the alias (next keyword delimits).
  { name := "alias_primitive", outcome := .verifies,
    why := "`type MyInt = int` resolves transitively; the alias really is `int`"
    src := r"
type MyInt = int
procedure u() opaque { var x: MyInt := 5; assert x == 5 };"},

  { name := "alias_primitive_wrong", outcome := .failsExactly 1,
    why := "a false assert through the primitive alias must FAIL (alias genuinely resolves to int)"
    src := r"
type MyInt = int
procedure u() opaque { var x: MyInt := 5; assert x == 6 };"},

  { name := "alias_chained", outcome := .verifies,
    why := "`type A = int; type B = A` resolves transitively"
    src := r"
type A = int
type B = A
procedure u() opaque { var x: B := 7; assert x == 7 };"},

  { name := "alias_map", outcome := .verifies,
    why := "`type IM = Map int bool` — select/const work through the alias"
    src := r"
type IM = Map int bool
procedure u() opaque { var m: IM := const(false); assert select(m, 9) == false };"},

  { name := "alias_composite_field", outcome := .verifies,
    why := "`type P = Pt` (composite) + field access `p#x` — the resolveFieldInTypeScope alias-unfold finds Pt's fields"
    src := r"
composite Pt { var x: int }
type P = Pt
procedure u() opaque { var p: P := new Pt; p#x := 3; assert p#x == 3 };"},

  { name := "alias_composite_field_wrong", outcome := .failsExactly 1,
    why := "a false read through a composite alias's field must FAIL (alias resolves to the real Pt field)"
    src := r"
composite Pt { var x: int }
type P = Pt
procedure u() opaque { var p: P := new Pt; p#x := 3; assert p#x == 4 };"},
  -- GENERIC type aliases (`type Foo<T> = …`). The alias's `<T>` binders substitute into the target
  -- at the instantiation; `TypeAliasElim` (now before monomorphize) and `TypeLattice.unfold` (the
  -- `.Applied`-alias arm) both perform the param substitution, so the consistency relation agrees
  -- with elimination. Aliases to Map/primitive and to generic composites are covered, with twins.
  { name := "generic_alias_map", outcome := .verifies,
    why := "`type MyPair<A,B> = Map A B` at <int,bool> substitutes to `Map int bool`; select works through it"
    src := r"
type MyPair<A,B> = Map A B
procedure u() opaque { var m: MyPair<int, bool> := const(false); assert select(m, 9) == false };"},

  { name := "generic_alias_map_wrong", outcome := .failsExactly 1,
    why := "a false read through the generic Map alias must FAIL (substitution is sound, not vacuous)"
    src := r"
type MyPair<A,B> = Map A B
procedure u() opaque { var m: MyPair<int, bool> := const(false); assert select(m, 9) == true };"},

  { name := "generic_alias_order", outcome := .verifies,
    why := "`type Swapped<A,B> = Map B A` at <int,bool> must substitute to `Map bool int` (param ORDER preserved)"
    src := r"
type Swapped<A,B> = Map B A
procedure u() opaque { var m: Swapped<int, bool> := const(5); assert select(m, true) == 5 };"},

  { name := "generic_alias_arity_wrong", outcome := .rejected,
    why := "a generic alias applied at the wrong arity (`MyPair<int>`) must fail loud"
    src := r"
type MyPair<A,B> = Map A B
procedure u() opaque { var m: MyPair<int> := const(false); assert true };"},
  -- Generic alias of a generic COMPOSITE — the gap-(ii) case (unfold `.Applied`-alias + reorder).
  { name := "generic_alias_composite", outcome := .verifies,
    why := "`type Foo<T> = Box<T>`; `var b: Foo<int> := new Box<int>` cross-spelling assignment verifies, field round-trips"
    src := r"
composite Box<T> { var val: T }
type Foo<T> = Box<T>
procedure u() opaque { var b: Foo<int> := new Box<int>; b#val := 7; assert b#val == 7 };"},

  { name := "generic_alias_composite_wrong", outcome := .failsExactly 1,
    why := "a false read through the generic-composite alias must FAIL"
    src := r"
composite Box<T> { var val: T }
type Foo<T> = Box<T>
procedure u() opaque { var b: Foo<int> := new Box<int>; b#val := 7; assert b#val == 8 };"},

  { name := "generic_alias_composite_param", outcome := .verifies,
    why := "pass a concrete `Box<int>` to a `Foo<int>` (= alias of Box<T>) param — cross-spelling consistency unfolds the alias; round-trips"
    src := r"
composite Box<T> { var val: T }
type Foo<T> = Box<T>
procedure take(b: Foo<int>) returns (r: int) opaque ensures r == b#val { r := b#val };
procedure u() opaque { var x: Box<int> := new Box<int>; x#val := 9; var g: int := take(x); assert g == 9 };"},

  { name := "generic_alias_wrong_arg", outcome := .rejected,
    why := "SOUNDNESS: a `Box<bool>` value must NOT satisfy a `Foo<int>` (= Box<int>) param — unfold-then-compare stays strict on the arg"
    src := r"
composite Box<T> { var val: T }
type Foo<T> = Box<T>
procedure take(b: Foo<int>) returns (r: int) opaque { r := 0 };
procedure u() opaque { var x: Box<bool> := new Box<bool>; var g: int := take(x); assert g == 0 };"},

  { name := "generic_alias_chained", outcome := .verifies,
    why := "chained generic aliases `type A<T> = Box<T>; type B<U> = A<U>` resolve transitively at B<int>"
    src := r"
composite Box<T> { var val: T }
type A<T> = Box<T>
type B<U> = A<U>
procedure u() opaque { var b: B<int> := new Box<int>; b#val := 5; assert b#val == 5 };"},
  -- CYCLIC generic alias must fail loud, NOT hang — pins the fuel/visited guards in
  -- resolveAliasType / TypeLattice.unfold / resolveFieldInTypeScope.unfoldAlias.
  { name := "generic_alias_cyclic", outcome := .rejected,
    why := "a cyclic generic alias `type A<T> = B<T>; type B<U> = A<U>` must fail loud (guards terminate), not loop"
    src := r"
type A<T> = B<T>
type B<U> = A<U>
procedure u() opaque { var x: A<int> := 0; assert true };"},
  -- NESTED Map-typed field (`Map int Map int int`, no-paren grammar): exercises the RECURSIVE
  -- `.TMap` arm of instTagCommon + the box fns (tag `Map$a2$int$Map$a2$int$int`). Read/write round-trips.
  { name := "nested_map_field", outcome := .verifies,
    why := "a nested-Map composite field round-trips — the recursive `.TMap` box-tag handles `Map int (Map int int)`"
    src := r"
composite H { var m: Map int Map int int }
procedure u() opaque { var h: H := new H; var inner: Map int int := update(select(h#m, 1), 2, 3); h#m := update(h#m, 1, inner); assert select(select(h#m, 1), 2) == 3 };"},

  { name := "nested_map_field_wrong", outcome := .failsExactly 1,
    why := "a false read of the nested-Map field must FAIL — the recursive tag is sound, not vacuous"
    src := r"
composite H { var m: Map int Map int int }
procedure u() opaque { var h: H := new H; var inner: Map int int := update(select(h#m, 1), 2, 3); h#m := update(h#m, 1, inner); assert select(select(h#m, 1), 2) == 4 };"},
  -- NESTED generic operand in `is` (`Box<Pair<int,bool>>`): the monomorph tag nests (`Box$a1$Pair$a2$int$bool`).
  { name := "is_nested_generic_operand", outcome := .verifies,
    why := "`b is Box<Pair<int,bool>>` against the matching instantiation verifies (nested `>>` operand)"
    src := r"
composite Box<T> { var val: T }
composite Pair<A,B> { var a: A }
procedure u() opaque { var b: Box<Pair<int,bool>> := new Box<Pair<int,bool>>; assert b is Box<Pair<int,bool>> };"},

  { name := "is_nested_generic_operand_wrong", outcome := .rejected (some .UserError),
    why := "`Box<Pair<int,bool>> is Box<Pair<bool,int>>` — wrong inner instantiation is unrelated, rejected (param order matters)"
    src := r"
composite Box<T> { var val: T }
composite Pair<A,B> { var a: A }
procedure u() opaque { var b: Box<Pair<int,bool>> := new Box<Pair<int,bool>>; assert b is Box<Pair<bool,int>> };"} ]

/-- Generic composites verify end-to-end via monomorphization — across every type position,
    nested generics (fixpoint worklist), explicit `new C<τ>`, and chained field writes. -/
def runGenericCompositeTest : IO Unit := checkCases genericCompositeCorpus

#guard_msgs (drop info, error) in
#eval runGenericCompositeTest

end Strata.Laurel
