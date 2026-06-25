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
# Generic method / inheritance / upcast tests

Generic composite methods (instance procedures), inheritance, upcasting, and field-type concretization.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-! ## Generic composite methods (instance procedures), inheritance, upcasting

A method on a generic composite — `composite Box<T> { var val: T; procedure
get(self: Box<T>) returns (r: T) … }` — is lifted (by `liftInstanceProceduresPass`,
moved before monomorphization) to a top-level POLY procedure carrying the composite's
type params (`Box$get<T>(self: Box<T>)`), which the procedure monomorphizer then
clones per call-site instantiation. So methods reuse the procedure-monomorphization
machinery with no new monomorphization. `extends` on a generic composite is still
rejected loud. -/
private def boxGet := r"
composite Box<T> {
  var val: T
  procedure get(self: Box<T>) returns (r: T) opaque ensures r == self#val { r := self#val };
}
"

-- Inheritance monomorphizes the child + parent (concrete or generic parent), topo-
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
    src := r"
composite Box<T> {
  var val: T
  procedure bad(self: Box<T>) returns (r: int) opaque ensures r == 0 { r := 1 };
}
procedure u() opaque { var bx: Box<int> := new Box<int>; var g: int := bx#bad(); assert 1 == 1 };"},

  { name := "generic_method_precond_gated", outcome := .failsExactly 1,
    why := "a violated precondition on `self#val` (caller sets 5, method requires 7) must GATE — exactly the precondition VC fails (caller asserts only 1==1)"
    src := r"
composite Box<T> {
  var val: T
  procedure get7(self: Box<T>) returns (r: T) requires self#val == 7 opaque ensures r == self#val { r := self#val };
}
procedure u() opaque { var bx: Box<int> := new Box<int>; bx#val := 5; var g: int := bx#get7(); assert 1 == 1 };"},
  -- A method declaring its OWN type param `<U>`, distinct from the composite's `T`: the
  -- lift carries BOTH (composite's ++ method's), monomorphized per call.
  { name := "method_own_typaram", outcome := .verifies,
    why := "a method's own type param `id2<U>` called at bool verifies (`U` binds to `bool`)"
    src := r"
composite Box<T> {
  var v: T
  procedure id2<U>(self: Box<T>, x: U) returns (r: U) opaque ensures r == x { r := x };
}
procedure u() opaque { var b: Box<int> := new Box<int>; var y: bool := b#id2(true); assert y == true };"},

  { name := "method_own_typaram_wrong", outcome := .failsExactly 1,
    why := "a FALSE postcondition on a method-own-typaram method must FAIL — sound, not vacuous"
    src := r"
composite Box<T> {
  var v: T
  procedure bad<U>(self: Box<T>, x: U) returns (r: int) opaque ensures r == 0 { r := 1 };
}
procedure u() opaque { var b: Box<int> := new Box<int>; var z: int := b#bad(true); assert 1 == 1 };"},

  { name := "method_own_typaram_multi", outcome := .verifies,
    why := "a method-own type param at int AND bool each monomorphize + verify"
    src := r"
composite Box<T> {
  var v: T
  procedure id2<U>(self: Box<T>, x: U) returns (r: U) opaque ensures r == x { r := x };
}
procedure u() opaque { var b: Box<int> := new Box<int>; var p: int := b#id2(7); var q: bool := b#id2(false); assert p == 7 && q == false };"},
  -- Inheritance — concrete parent (`Box<T> extends Base`): child monomorphizes to
  -- `Box$int extends Base`, emitted AFTER the parent so re-resolution builds the parent's
  -- field-inheritance scope first (the parent-before-child emission-order fix).
  { name := "generic_extends_concrete_parent", outcome := .verifies,
    why := "`Box<T> extends Base` (concrete parent) monomorphizes + inherits `tag`, verifies"
    src := r"
composite Base { var tag: int }
composite Box<T> extends Base { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 1; b#val := 7; assert b#tag == 1 && b#val == 7 };"},

  { name := "generic_extends_concrete_parent_wrong", outcome := .failsExactly 1,
    why := "a wrong INHERITED-field value must FAIL — checked, not vacuously havoc'd (the bug fixed here)"
    src := r"
composite Base { var tag: int }
composite Box<T> extends Base { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 1; assert b#tag == 2 };"},
  -- Inheritance — generic parent at an instantiation (`Box<T> extends Base<T>`): the
  -- monomorphizer collects the parent inst and topo-orders `Base$int` before `Box$int`.
  -- Needed for idiomatic Java (generic-class-extends-generic-class).
  { name := "generic_extends_generic_parent", outcome := .verifies,
    why := "`Box<T> extends Base<T>` → `Box$int extends Base$int`, inherits `tag:T`→int, verifies"
    src := r"
composite Base<T> { var tag: T }
composite Box<T> extends Base<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 1; b#val := 7; assert b#tag == 1 && b#val == 7 };"},

  { name := "generic_extends_generic_parent_wrong", outcome := .failsExactly 1,
    why := "a wrong value on the generic-parent's inherited field must FAIL"
    src := r"
composite Base<T> { var tag: T }
composite Box<T> extends Base<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 1; assert b#tag == 2 };"},

  { name := "generic_extends_generic_parent_multi", outcome := .verifies,
    why := "`Box<int>`/`Box<bool>` get distinct parent monomorphs `Base$int`/`Base$bool`"
    src := r"
composite Base<T> { var tag: T }
composite Box<T> extends Base<T> { var val: T }
procedure u() opaque { var bi: Box<int> := new Box<int>; bi#tag := 9; var bb: Box<bool> := new Box<bool>; bb#tag := true; assert bi#tag == 9 && bb#tag == true };"},
  { name := "generic_upcast_same_inst", outcome := .verifies,
    why := "`Box<int>` → `Base<int>` (same-inst upcast) verifies, reading the inherited tag"
    src := r"
composite Base<T> { var tag: T }
composite Box<T> extends Base<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; b#tag := 5; var p: Base<int> := b; assert p#tag == 5 };"},
  -- REMAP upcast: `P2<A,B> extends Pair<B,A>` so `P2<int,bool>`'s parent is `Pair<bool,int>`
  -- (inherited `fst:bool`, `snd:int`). Reads values back through the parent — guards
  -- VALUE-PRESERVATION through the remap, the exact property the reverted unsound upcast broke.
  { name := "generic_upcast_remap", outcome := .verifies,
    why := "`P2<int,bool>` → `Pair<bool,int>` verifies with values preserved through the remap"
    src := r"
composite Pair<A,B> { var fst: A var snd: B }
composite P2<A,B> extends Pair<B,A> { var extra: int }
procedure u() opaque { var x: P2<int,bool> := new P2<int,bool>; x#fst := true; x#snd := 9; var p: Pair<bool,int> := x; assert p#fst == true && p#snd == 9 };"},

  { name := "generic_upcast_remap_wrong_value", outcome := .failsExactly 1,
    why := "a WRONG value read back through the remapped upcast must FAIL (not vacuous)"
    src := r"
composite Pair<A,B> { var fst: A var snd: B }
composite P2<A,B> extends Pair<B,A> { var extra: int }
procedure u() opaque { var x: P2<int,bool> := new P2<int,bool>; x#snd := 9; var p: Pair<bool,int> := x; assert p#snd == 8 };"},
  -- CONCRETIZATION upcast: `Box<T> extends Base<int>` so `Box<bool>`'s parent is `Base<int>`.
  { name := "generic_upcast_concretization", outcome := .verifies,
    why := "`Box<bool> extends Base<int>` → `Base<int>` verifies with the concretized field preserved"
    src := r"
composite Base<S> { var b: S }
composite Box<T> extends Base<int> { var v: T }
procedure u() opaque { var x: Box<bool> := new Box<bool>; x#b := 7; var p: Base<int> := x; assert p#b == 7 };"},

  { name := "generic_upcast_concretization_wrong_value", outcome := .failsExactly 1,
    why := "a WRONG concretized-field value must FAIL"
    src := r"
composite Base<S> { var b: S }
composite Box<T> extends Base<int> { var v: T }
procedure u() opaque { var x: Box<bool> := new Box<bool>; x#b := 7; var p: Base<int> := x; assert p#b == 6 };"},
  -- Upcast MUST-REJECTs — the unsoundnesses the adversarial pass found, now closed.
  { name := "generic_upcast_wrong_inst", outcome := .rejected,
    why := "`Box<int>` into a `Base<bool>` var must be REJECTED (wrong instantiation)"
    src := r"
composite Base<T> { var tag: T }
composite Box<T> extends Base<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; var p: Base<bool> := b; assert 1 == 1 };"},

  { name := "generic_upcast_remap_wrong_target", outcome := .rejected,
    why := "`P2<int,bool> extends Pair<B,A>` upcast to the WRONG `Pair<int,bool>` (true supertype `Pair<bool,int>`) must be REJECTED — the unsound wrong-accept that ignored the extends remap"
    src := r"
composite Pair<A,B> { var fst: A var snd: B }
composite P2<A,B> extends Pair<B,A> { var extra: int }
procedure u() opaque { var x: P2<int,bool> := new P2<int,bool>; var p: Pair<int,bool> := x; assert 1 == 1 };"},

  { name := "generic_upcast_concretization_wrong_target", outcome := .rejected,
    why := "`Box<bool> extends Base<int>` upcast to `Base<bool>` must be REJECTED (supertype is `Base<int>`) — the other concretization wrong-accept"
    src := r"
composite Base<S> { var b: S }
composite Box<T> extends Base<int> { var v: T }
procedure u() opaque { var x: Box<bool> := new Box<bool>; var p: Base<bool> := x; assert 1 == 1 };"},

  { name := "generic_upcast_unrelated", outcome := .rejected,
    why := "`Box<int>` into an UNRELATED `Other<int>` var must be REJECTED"
    src := r"
composite Other<T> { var o: T }
composite Base<T> { var tag: T }
composite Box<T> extends Base<T> { var val: T }
procedure u() opaque { var b: Box<int> := new Box<int>; var p: Other<int> := b; assert 1 == 1 };"},
  -- DIAMOND on a GENERIC receiver: a field inherited via two paths (`D<T>` extends both
  -- `L<T>` and `R<T>`, each extending `Top<T>`) is ambiguous and the access must be REJECTED.
  -- The receiver is `D<int>` (an `.Applied` type), so the diamond check must peel the base
  -- name — else the access is missed pre-monomorphization and surfaces as an internal error
  -- when the monomorph re-resolves.
  { name := "diamond_field_generic_receiver", outcome := .rejected,
    why := "a diamond-inherited field read on a generic receiver `D<int>` must be REJECTED cleanly (peel `.Applied` to base name), not an internal error"
    src := r"
composite Top<T> { var f: T }
composite L<T> extends Top<T> { }
composite R<T> extends Top<T> { }
composite D<T> extends L<T>, R<T> { }
procedure u() opaque { var d: D<int> := new D<int>; var x: int := d#f; assert 1 == 1 };"},
  -- Field-type concretization (reject-only): a `.TVar` field is checked against the holder's
  -- concrete instantiation by substituting the DECLARING composite's params (own field: holder
  -- args; inherited: via `substitutedAncestors`, remap-aware). Can never create a false accept;
  -- the IDENTITY on polymorphic code (holder at `.TVar` args ⇒ field stays `.TVar`).
  { name := "field_tvar_own_write_wrong", outcome := .rejected,
    why := "writing an `Other` into `g#h` (g: GHolder<Pair<int,bool>>, field `h:T` = `Pair<int,bool>`) must be REJECTED"
    src := r"
composite Pair<X,Y> { var a: X var b: Y }
composite Other { var z: int }
composite GHolder<T> { var h: T }
procedure u(g: GHolder<Pair<int,bool>>) opaque modifies g { var o: Other := new Other; g#h := o };"},

  { name := "field_tvar_own_read_wrong", outcome := .rejected,
    why := "reading `g#h` (= `Pair<int,bool>`) into an `Other` local must be REJECTED"
    src := r"
composite Pair<X,Y> { var a: X var b: Y }
composite Other { var z: int }
composite GHolder<T> { var h: T }
procedure u(g: GHolder<Pair<int,bool>>) opaque { var o: Other := g#h };"},

  { name := "field_tvar_inherited_write_wrong", outcome := .rejected,
    why := "writing `Other` into inherited `g#h` (Base<T>.h = `Pair<int,bool>`) must be REJECTED (inherited concretization)"
    src := r"
composite Pair<X,Y> { var a: X var b: Y }
composite Other { var z: int }
composite Base<T> { var h: T }
composite GHolder<T> extends Base<T> { var k: int }
procedure u(g: GHolder<Pair<int,bool>>) opaque modifies g { var o: Other := new Other; g#h := o };"},

  { name := "field_tvar_own_correct", outcome := .verifies,
    why := "writing/reading a `Pair<int,bool>` through `g#h` (correct type) must STILL translate (not over-rejected)"
    src := r"
composite Pair<X,Y> { var a: X var b: Y }
composite GHolder<T> { var h: T }
procedure u(g: GHolder<Pair<int,bool>>) opaque modifies g { var p: Pair<int,bool> := new Pair<int,bool>; g#h := p; var q: Pair<int,bool> := g#h; assert 1 == 1 };"},

  { name := "field_tvar_inherited_correct", outcome := .verifies,
    why := "writing a `Pair<int,bool>` through inherited `g#h` (correct type) must STILL translate"
    src := r"
composite Pair<X,Y> { var a: X var b: Y }
composite Base<T> { var h: T }
composite GHolder<T> extends Base<T> { var k: int }
procedure u(g: GHolder<Pair<int,bool>>) opaque modifies g { var p: Pair<int,bool> := new Pair<int,bool>; g#h := p; assert 1 == 1 };"},
  { name := "field_tvar_inherited_remap_write_wrong", outcome := .rejected,
    why := "with the `extends Base<B,A>` remap, inherited `g#h` at `GHolder<int,bool>` is `bool`; writing `7` must be REJECTED"
    src := r"
composite Base<U,V> { var h: U }
composite GHolder<A,B> extends Base<B,A> { var k: int }
procedure u(g: GHolder<int,bool>) opaque modifies g { g#h := 7 };"},

  { name := "concrete_extends_geninst_upcast", outcome := .verifies,
    why := "`IntBox extends Box<int>`: upcast to `Box<int>` + read the inherited field `val` through it verifies"
    src := r"
composite Box<T> { var val: T }
composite IntBox extends Box<int> { var w: int }
procedure u() opaque { var ib: IntBox := new IntBox; ib#val := 5; var b: Box<int> := ib; var got: int := b#val; assert got == 5 };"},

  { name := "concrete_extends_geninst_inherited_direct", outcome := .verifies,
    why := "inherited field read on the concrete child directly (no upcast) — the topo-sort places the monomorph parent first"
    src := r"
composite Box<T> { var val: T }
composite IntBox extends Box<int> { var w: int }
procedure u() opaque { var ib: IntBox := new IntBox; ib#val := 5; assert ib#val == 5 };"},

  { name := "concrete_extends_geninst_transitive", outcome := .verifies,
    why := "3-level mixed chain `Super extends IntBox extends Box<int>`: upcast Super to Box<int> reads the inherited field (whole-list topo sort handles the transitive concrete→monomorph order)"
    src := r"
composite Box<T> { var val: T }
composite IntBox extends Box<int> { var w: int }
composite Super extends IntBox { var z: int }
procedure u() opaque { var s: Super := new Super; s#val := 9; var b: Box<int> := s; assert b#val == 9 };"},

  { name := "concrete_extends_geninst_wrong_target", outcome := .rejected,
    why := "`IntBox extends Box<int>` upcast to the WRONG instantiation `Box<bool>` must be REJECTED — the new subtype arm compares the SUBSTITUTED ancestor `Box<int>` with invariant args, so `Box<bool>` fails"
    src := r"
composite Box<T> { var val: T }
composite IntBox extends Box<int> { var w: int }
procedure u() opaque { var ib: IntBox := new IntBox; var b: Box<bool> := ib; assert 1 == 1 };"},

  { name := "concrete_extends_geninst_remap_swap", outcome := .rejected,
    why := "`W extends Pair<int,bool>` upcast to the SWAPPED `Pair<bool,int>` must be REJECTED (the prior-bug shape) — substituted ancestor `Pair<int,bool>` ≠ `Pair<bool,int>`"
    src := r"
composite Pair<A,B> { var a: A var b: B }
composite W extends Pair<int,bool> { var w: int }
procedure u() opaque { var x: W := new W; var p: Pair<bool,int> := x; assert 1 == 1 };"},

  { name := "concrete_extends_geninst_false_twin", outcome := .failsExactly 1,
    why := "a FALSE inherited-field read through the upcast must FAIL — the upcast is sound, not vacuous"
    src := r"
composite Box<T> { var val: T }
composite IntBox extends Box<int> { var w: int }
procedure u() opaque { var ib: IntBox := new IntBox; ib#val := 5; var b: Box<int> := ib; var got: int := b#val; assert got == 6 };"},

  { name := "as_guarded_downcast_heap_neutral", outcome := .verifies,
    why := "`if (p is Child) then ... p as Child ...` in a heap-neutral opaque proc on an opaque `Parent` param translates + verifies (was NotYetImplemented before the heap-neutral AsType-lowering fix); the guard discharges the cast's is-obligation"
    src := r"
composite Parent { var x: int }
composite Child extends Parent { var y: int }
procedure d(p: Parent) returns (r: int) opaque ensures true { if (p is Child) then { var c: Child := p as Child; r := c#y } else { r := 0 } };
procedure u() opaque { var b: Parent := new Child; var got: int := d(b); assert 1 == 1 };"},

  { name := "as_unguarded_downcast_guard_fails", outcome := .failsExactly 1,
    why := "`p as Child` on an opaque `Parent` param (not provably a `Child`) FAILS the lowered is-guard — proves the heap-neutral `as` lowering ran AND the downcast obligation is real"
    src := r"
composite Parent { var x: int }
composite Child extends Parent { var y: int }
procedure d(p: Parent) returns (r: int) opaque ensures true { var c: Child := p as Child; r := c#y };
procedure u() opaque { var got: int := d(new Parent); assert 1 == 1 };"},
]

def runGenericMethodTest : IO Unit := checkCases genericMethodCorpus

#guard_msgs (drop info, error) in
#eval runGenericMethodTest

end Strata.Laurel
