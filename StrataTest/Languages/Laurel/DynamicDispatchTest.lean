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
# Dynamic dispatch + behavioral-subtyping (Liskov) corpus

The feature corpus for dynamic method dispatch and the behavioral-subtyping
(Liskov) check that makes it sound. Driven by the shared `Case`/`checkCase`
harness (`StrataTest.Util.LaurelCorpusHarness`), with must-fail twins pinning soundness.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-! ## Dynamic dispatch + behavioral subtyping (Liskov)

Method dispatch is VIRTUAL: a call on a statically-`Parent`-typed receiver holding a
more-derived value runs the derived override (`LiftInstanceProcedures` generates a
runtime-tag dispatcher `Parent$m` over `Parent$m$impl`/`Child$m$impl`, with
tag-conditioned postconditions). This is sound because `CheckOverrideRefinement` (the
Liskov pass) rejects any override whose contract does not refine its parent's. GENERIC
inheriting families are included (the dispatcher/checker carry the composite's type
params and monomorphize per instantiation; see `generic_dispatch_*` below).
-/

def dynamicDispatchCorpus : List Case := [
  { name := "dispatch_parent_holds_child", outcome := .verifies,
    why := "`b: Parent := new Child; b#m()` runs Child's override (r==2) — dynamic dispatch through a static Parent reference"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { var b: Parent := new Child; var r: int := b#m(); assert r == 2 };"},

  { name := "dispatch_parent_holds_child_wrong", outcome := .failsExactly 1,
    why := "the same call does NOT return the Parent value (1) — dispatch is dynamic, so asserting r==1 must FAIL"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { var b: Parent := new Child; var r: int := b#m(); assert r == 1 };"},
  { name := "dispatch_modular_sound", outcome := .verifies,
    why := "`helper(b: Parent) ensures out>=0 { out := b#m() }` called with a Child verifies — the override (r==2) refines Parent's (r>=0), so the modular guarantee holds under dynamic dispatch"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure helper(b: Parent) returns (out: int) opaque ensures out >= 0 { out := b#m() };
procedure u() opaque { var c: Child := new Child; var got: int := helper(c); assert got >= 0 };"},
  { name := "dispatch_three_level", outcome := .verifies,
    why := "3-level refining hierarchy (r>=0 ⊇ r>=1 ⊇ r>=2): GP-typed holding a C dispatches soundly, GP's contract r>=0 holds"
    src := r"
composite GP { var g: int
  procedure m(self: GP) returns (r: int) opaque ensures r >= 0 { r := 5 };
}
composite P extends GP {
  procedure m(self: P) returns (r: int) opaque ensures r >= 1 { r := 5 };
}
composite C extends P {
  procedure m(self: C) returns (r: int) opaque ensures r >= 2 { r := 5 };
}
procedure u() opaque { var x: GP := new C; var r: int := x#m(); assert r >= 0 };"},
  { name := "liskov_weaker_post_rejected", outcome := .failsExactly 1,
    why := "Child.m `ensures r == -5` does NOT refine Parent.m `ensures r >= 0` — the override-refinement (Liskov) check FAILS"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == -5 { r := -5 };
}
procedure u() opaque { assert 1 == 1 };"},
  { name := "liskov_stronger_pre_rejected", outcome := .failsExactly 2,
    why := "Child.m `requires a >= 5` is STRONGER than Parent.m `requires a >= 0` — contravariance FAILS (the pre-refinement checker fails; a 2nd VC from the dispatcher path also surfaces — both reject)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 0 opaque ensures true { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 5 opaque ensures true { r := 1 };
}
procedure u() opaque { assert 1 == 1 };"},
  { name := "liskov_sound_override", outcome := .verifies,
    why := "Child.m `ensures r == 2` refines Parent.m `ensures r >= 0` (2>=0) — the override-refinement check passes"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 5 opaque ensures r >= 0 { r := 2 };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 0 opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { assert 1 == 1 };"},
  -- POST-COVARIANCE UNDER THE PARENT PRECONDITION: Child.m `ensures r == a` refines
  -- Parent.m `ensures r >= 0` ONLY when `a >= 0` (the parent's `requires`). The post-checker
  -- must ASSUME Parent.pre — else this sound override is spuriously over-rejected.
  { name := "liskov_post_covariance_under_parent_pre", outcome := .verifies,
    why := "`Child.post (r==a)` implies `Parent.post (r>=0)` under `Parent.pre (a>=0)`; the post-checker assumes Parent.pre so the sound override verifies"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 0 opaque ensures r >= 0 { r := a };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 0 opaque ensures r == a { r := a };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "liskov_post_covariance_violation_under_pre", outcome := .failsExactly 1,
    why := "even WITH `Parent.pre (a>=0)` assumed, `Child.post (r==a-100)` can be negative, so it does NOT refine `Parent.post (r>=0)` — must still be REJECTED (the Parent.pre assumption must not weaken the checker into accepting real violations)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 0 opaque ensures r >= 0 { r := a };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 0 opaque ensures r == a - 100 { r := a - 100 };
}
procedure u() opaque { assert 1 == 1 };"},
  { name := "dispatch_three_level_false", outcome := .failsExactly 1,
    why := "a false assertion (r>=100) on a dynamically-dispatched 3-level call must FAIL — dispatch is sound, not vacuous"
    src := r"
composite GP { var g: int
  procedure m(self: GP) returns (r: int) opaque ensures r >= 0 { r := 5 };
}
composite P extends GP {
  procedure m(self: P) returns (r: int) opaque ensures r >= 1 { r := 5 };
}
composite C extends P {
  procedure m(self: C) returns (r: int) opaque ensures r >= 2 { r := 5 };
}
procedure u() opaque { var x: GP := new C; var r: int := x#m(); assert r >= 100 };"},

  -- LINEAR-CHAIN MIDDLE-ANCESTOR violation: `C.m` refines its GRANDPARENT `GP` (r>=0) but
  -- VIOLATES its direct parent `P` (r>=5) with `ensures r == 2`. `findOverriddenParents`
  -- walks ALL strict ancestors (not just the nearest), so it emits a checker set for BOTH
  -- `C`-vs-`GP` (holds) and `C`-vs-`P` (fails). The 3-level cases above are all-refining and
  -- the diamond cases use DIRECT parents; this is the only case pinning the all-ancestors
  -- contract on a LINEAR chain — exactly `.failsExactly 1` (the C-vs-P checker), not 0.
  { name := "linear_middle_ancestor_violation_rejected", outcome := .failsExactly 2,
    why := "`C.m ensures r == 2` refines grandparent `GP` (r>=0) but violates direct parent `P` (r>=5). TWO surfaces catch it: the definition-time C-vs-P refinement checker (findOverriddenParents checks C against EVERY ancestor, not just nearest — the point of this case), AND the `P` dispatcher's own tag-conditioned post for its `C` branch (`P$m` dispatches over `{C}`, whose owner post asserts P's `r>=5` on a value that returns 2). Both are sound rejections of the same violation"
    src := r"
composite GPlin { var g: int
  procedure m(self: GPlin) returns (r: int) opaque ensures r >= 0 { r := 5 };
}
composite Plin extends GPlin {
  procedure m(self: Plin) returns (r: int) opaque ensures r >= 5 { r := 5 };
}
composite Clin extends Plin {
  procedure m(self: Clin) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { assert 1 == 1 };"},

  -- SKIP-LEVEL override: `GPskip` declares `m`, the intermediate `Pskip` does NOT override
  -- it, and the leaf `Cskip` does. `descendantOverriders` must find `Cskip` as an overrider of
  -- `GPskip.m` while skipping the non-overriding `Pskip`, so a `GPskip`-typed ref holding a
  -- `Cskip` dispatches to `Cskip$m$impl`. A natural Java shape the all-refining 3-level case
  -- does not exercise (there every level overrides).
  { name := "skip_level_override_dispatches", outcome := .verifies,
    why := "`GPskip` declares `m`, intermediate `Pskip` does not override, leaf `Cskip` does — descendantOverriders skips the non-overriding intermediate and dispatches a `GPskip`-typed `Cskip` to the leaf override; `GP`'s contract `r>=0` holds"
    src := r"
composite GPskip { var g: int
  procedure m(self: GPskip) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Pskip extends GPskip { var p: int }
composite Cskip extends Pskip {
  procedure m(self: Cskip) returns (r: int) opaque ensures r >= 3 { r := 3 };
}
procedure u() opaque { var x: GPskip := new Cskip; var r: int := x#m(); assert r >= 0 };"},

  -- COLLECTION-TYPED PARAMETER: `m`'s non-`self` param is a `TotalMap int int`. Family membership
  -- (`isOverrideOf` → `sameNonSelfSignature` → `typeMatchesModuloTVars`) must recurse through
  -- the `.TMap` arm to see the override's param type matches the base's, so the pair forms a
  -- dispatch family and the override is checked + dispatched. The `.Applied`/primitive param
  -- cases above never exercise the `.TMap` recursion. (`.TSet` has no surface production —
  -- `TotalMap` is the only `.TMap`-producing type — so `.TSet` is unreachable and not covered.)
  { name := "map_param_override_dispatches", outcome := .verifies,
    why := "`Base.m(self, d: TotalMap int int)` overridden by `Sub.m(self, d: TotalMap int int)` — the map-typed param matches through `typeMatchesModuloTVars`' `.TMap` arm, so the family forms; a `Base`-typed ref holding a `Sub` dispatches to the override and its `r >= 0` holds"
    src := r"
composite Base { var x: int
  procedure m(self: Base, d: TotalMap int int) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Sub extends Base {
  procedure m(self: Sub, d: TotalMap int int) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
procedure u() opaque { var b: Base := new Sub; var d: TotalMap int int; var r: int := b#m(d); assert r >= 0 };"},

  -- GATE-CONSISTENCY (unified dispatch/checker gate): a method with
  -- an `.Applied`-typed parameter (`b: Box<int>`) is dispatched virtually, so it
  -- MUST be Liskov-checked. Both passes gate on the single `isVirtualDispatchMethod`,
  -- so a violating override (r==-1 vs r>=0) is REJECTED — a checker that instead keys
  -- on parameter types (skipping on `.Applied`) while the dispatcher keys on composite
  -- type params would diverge and silently ACCEPT it.
  { name := "liskov_applied_param_violation_caught", outcome := .failsExactly 1,
    why := "a Liskov-violating override on a method with an `.Applied` (`Box<int>`) parameter is caught — the dispatch gate and the refinement-checker gate are unified (a single gate keeps them from diverging)"
    src := r"
composite Box<T> { var val: T }
composite Parent { var x: int
  procedure m(self: Parent, b: Box<int>) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, b: Box<int>) returns (r: int) opaque ensures r == 0 - 1 { r := 0 - 1 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "liskov_applied_param_sound_ok", outcome := .verifies,
    why := "a SOUND override on an `.Applied`-param method still verifies (the unified gate does not over-reject)"
    src := r"
composite Box<T> { var val: T }
composite Parent { var x: int
  procedure m(self: Parent, b: Box<int>) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, b: Box<int>) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { assert 1 == 1 };"},
  -- GENERIC dynamic dispatch: a method on a GENERIC composite, overridden by a generic
  -- subtype, dispatches virtually. The dispatcher's is/as tag-tests use the applied
  -- form (`self is SBox<int>`) and the Liskov checker carries the composite's type
  -- params so it monomorphizes per instantiation.
  { name := "generic_dispatch_runtime_override", outcome := .verifies,
    why := "`b: Box<int> := new SBox<int>; b#get()` runs SBox's override (r==7) through a generic Box<int> reference — dynamic dispatch over a generic family"
    src := r"
composite Box<T> { var val: T
  procedure get(self: Box<T>) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: int) opaque ensures r == 7 { r := 7 };
}
procedure u() opaque { var b: Box<int> := new SBox<int>; var r: int := b#get(); assert r == 7 };"},

  { name := "generic_dispatch_runtime_override_wrong", outcome := .failsExactly 1,
    why := "the generic dynamic call does NOT return the parent value (0) — dispatch is dynamic"
    src := r"
composite Box<T> { var val: T
  procedure get(self: Box<T>) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: int) opaque ensures r == 7 { r := 7 };
}
procedure u() opaque { var b: Box<int> := new SBox<int>; var r: int := b#get(); assert r == 0 };"},

  { name := "generic_liskov_violation_caught", outcome := .failsExactly 1,
    why := "a Liskov-violating override on a GENERIC family (SBox.get `ensures r == -5` not refining Box.get `ensures r >= 0`) is caught — generic Liskov checking applies per instantiation"
    src := r"
composite Box<T> { var val: T
  procedure get(self: Box<T>) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: int) opaque ensures r == 0 - 5 { r := 0 - 5 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "generic_dispatch_multi_instantiation", outcome := .verifies,
    why := "the same generic virtual method dispatched at TWO instantiations (Box<int> and Box<bool> holding SBox) — distinct monomorphs, both dispatch correctly"
    src := r"
composite Box<T> { var val: T
  procedure get(self: Box<T>) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: int) opaque ensures r == 7 { r := 7 };
}
procedure u() opaque { var bi: Box<int> := new SBox<int>; var ri: int := bi#get(); var bb: Box<bool> := new SBox<bool>; var rb: int := bb#get(); assert ri == 7 && rb == 7 };"},
  -- VOID heap-MUTATING method, dispatched. For a void method that is BOTH overridden AND a
  -- heap-writer (`modifies`), the dispatcher's `then` branch is a block, so the `else`
  -- fallthrough must be block-wrapped too — otherwise the two branches synthesize
  -- different types for the `$heap`-threaded void call ("'if' branches have incompatible
  -- types 'Heap' and 'void'"). Block-wrapping the fallthrough keeps the branches symmetric.
  { name := "void_heapwriter_dispatch_translates", outcome := .verifies,
    why := "a void heap-mutating method that is overridden + dispatched translates + verifies (dispatcher fallthrough block-wrapped for branch-type symmetry)"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert cc#v == 1 };"},

  { name := "void_heapwriter_dispatch_wrong", outcome := .failsExactly 1,
    why := "the void heap-writer dispatch conveys the override's postcondition (c#v == 1), so a false read (c#v == 2) must FAIL"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert cc#v == 2 };"},
  -- MIXED modifies-status across a dispatched family: an empty-bodied parent method that
  -- declares `modifies c`, and an override that actually writes `c`. Under the global-heap
  -- model each dispatcher branch is a STATEMENT (`$heap := O$m$impl($heap, ..)` for a
  -- writer, a void `T$m$impl(..)` otherwise), never an expression carrying a `Heap` value,
  -- so there is no "`Heap` vs void" branch type-join to reconcile — the family translates
  -- with no special heap-status unification. The parent declares `modifies c` too, so the
  -- override does not WIDEN the frame (a frame-widening override is a Liskov
  -- modifies-violation, covered by mixed_modifies_frame_widen_rejected below).
  { name := "mixed_modifies_dispatch_translates", outcome := .verifies,
    why := "a dispatched family where the parent method has an empty body but declares `modifies c` and the override mutates c — mixed heap-touching shape — translates + the override's post is conveyed through the upcast"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures true modifies c { };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert cc#v == 1 };"},

  { name := "mixed_modifies_frame_widen_rejected", outcome := .failsExactly 2,
    why := "an override that WIDENS the modifies frame (parent modifies nothing, child modifies c) is a Liskov frame-violation, caught TWICE: (1) the dispatcher call-site cannot prove the parent's (empty) frame when the override mutates c, and (2) the two-state-faithful post-checker (CheckOverrideRefinement) independently rejects it at definition time — its parent-frame `ensures` over the child-spec-havoc'd heap cannot prove `c` unchanged. Both are correct rejections of the same violation"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures true { };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == 1 modifies c { c#v := 1 };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert 1 == 1 };"},

  -- FRAMED-VOID PARENT with NO postcondition: parent declares `modifies c` (a real frame) but no
  -- `ensures`, and the override WIDENS to `modifies c, d`. The post-checker's covariance gate is
  -- `parentPosts.isEmpty` — empty here — but the modifies-subset obligation is independent of
  -- posts, so it must still fire on the parent's real frame (gated on `parentModifies` naming a
  -- target, not on posts). Pins that the definition-time frame check is emitted for a post-less
  -- framed parent — the defense-in-depth that a posts-only gate would skip. Also caught at the
  -- dispatch call site, hence failsExactly 2 (checker + call-site frame post).
  { name := "framed_void_parent_no_post_widen_rejected", outcome := .failsExactly 2,
    why := "parent `m modifies c` with NO postcondition, override widens to `modifies c, d` — a frame-widening Liskov violation. The definition-time post-checker fires on the parent's real `modifies` frame (independent of the empty postcondition set) AND the dispatcher call site rejects it; both correctly reject the widened frame"
    src := r"
composite Cell2 { var v: int }
composite ParentF { var x: int
  procedure m(self: ParentF, c: Cell2, d: Cell2) opaque modifies c { c#v := 1 };
}
composite ChildF extends ParentF {
  procedure m(self: ChildF, c: Cell2, d: Cell2) opaque modifies c, d { c#v := 1; d#v := 2 };
}
procedure u() opaque { var b: ParentF := new ChildF; var p: Cell2 := new Cell2; var q: Cell2 := new Cell2; b#m(p, q); assert 1 == 1 };"},
  -- TWO-STATE (`old(...)`) Liskov refinement. The post-checker is two-state-faithful: it
  -- calls a heap-writer `$childspec` companion so it gains an inout `$heap` and `old()`
  -- survives `PushOldInward`. Without that, `old(c#v)` would collapse to the current heap
  -- and any two-state override contract would be checked VACUOUSLY. These pin that a
  -- violating two-state override is REJECTED and a sound one still VERIFIES. (Definition-only
  -- — `u` just asserts 1==1 — so the outcome is the static checker's, in isolation.)
  { name := "old_liskov_weaker_post_rejected", outcome := .failsExactly 1,
    why := "Child.m `ensures c#v == old(c#v) - 1` (decrements) does NOT refine Parent.m `ensures c#v >= old(c#v)` (non-decreasing) — the two-state post-checker rejects it"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v >= old(c#v) modifies c { c#v := c#v + 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == old(c#v) - 1 modifies c { c#v := c#v - 1 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "old_liskov_sound_override_ok", outcome := .verifies,
    why := "Child.m `ensures c#v == old(c#v) + 2` refines Parent.m `ensures c#v >= old(c#v)` (a +2 increase satisfies non-decreasing) — the two-state post-checker accepts it (no over-rejection)"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v >= old(c#v) modifies c { c#v := c#v + 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == old(c#v) + 2 modifies c { c#v := c#v + 2 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "old_liskov_nested_old_rejected", outcome := .failsExactly 1,
    why := "nested `old(old(c#v))` (idempotent with `old(c#v)`): Child decrements, Parent requires non-decrease — still rejected, so the two-state machinery handles nested old correctly"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures c#v >= old(old(c#v)) modifies c { c#v := c#v + 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures c#v == old(c#v) - 1 modifies c { c#v := c#v - 1 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "old_liskov_generic_family_rejected", outcome := .failsExactly 1,
    why := "a two-state Liskov violation on a GENERIC family (the post-checker + its `$childspec` companion carry the composite's type params and monomorphize per instantiation) is rejected"
    src := r"
composite Cell { var v: int }
composite Box<T> { var b: T
  procedure m(self: Box<T>, c: Cell) opaque ensures c#v >= old(c#v) modifies c { c#v := c#v + 1 };
}
composite SBox<T> extends Box<T> {
  procedure m(self: SBox<T>, c: Cell) opaque ensures c#v == old(c#v) - 1 modifies c { c#v := c#v - 1 };
}
procedure u() opaque { var b: Box<int> := new SBox<int>; assert 1 == 1 };"},
  -- SIBLING / non-linear hierarchy: two incomparable children both override m — equal-distance
  -- siblings, exercising the name-tiebreaker path that makes sibling dispatch order deterministic.
  -- (Branch order is irrelevant to correctness here: dispatch is by runtime tag, and a value `is`
  -- exactly one sibling's type.) A Parent-typed var holding Child2 must run Child2.m.
  { name := "dispatch_sibling_holds_child2", outcome := .verifies,
    why := "Parent with two incomparable overriders C1/C2; a Parent-typed var holding a C2 dispatches to C2.m (r==3) by runtime tag — exercises equal-distance-sibling dispatch"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child1 extends Parent {
  procedure m(self: Child1) returns (r: int) opaque ensures r == 2 { r := 2 };
}
composite Child2 extends Parent {
  procedure m(self: Child2) returns (r: int) opaque ensures r == 3 { r := 3 };
}
procedure u() opaque { var b: Parent := new Child2; var r: int := b#m(); assert r == 3 };"},

  { name := "dispatch_sibling_holds_child2_wrong", outcome := .failsExactly 1,
    why := "holding a C2 does NOT run C1's override — asserting C1's value (r==2) must FAIL (dispatch picks the runtime tag, not an arbitrary sibling)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child1 extends Parent {
  procedure m(self: Child1) returns (r: int) opaque ensures r == 2 { r := 2 };
}
composite Child2 extends Parent {
  procedure m(self: Child2) returns (r: int) opaque ensures r == 3 { r := 3 };
}
procedure u() opaque { var b: Parent := new Child2; var r: int := b#m(); assert r == 2 };"},
  -- MULTI-OUTPUT dispatched method (returns two values): a distinct dispatcher path
  -- (`.Assign` over a list of output targets) and tag-conditioned posts over both outputs.
  { name := "dispatch_multi_output", outcome := .verifies,
    why := "an overridden method returning (a, b) dispatches with both outputs recovered through the static Parent reference (a==5)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (a: int, b: int) opaque ensures a >= 0 { a := 1; b := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (a: int, b: int) opaque ensures a == 5 { a := 5; b := 6 };
}
procedure u() opaque { var o: Parent := new Child; assign var p: int, var q: int := o#m(); assert p == 5 };"},

  { name := "dispatch_multi_output_wrong", outcome := .failsExactly 1,
    why := "the multi-output dispatch returns the override's first value (5), not the parent's (1) — asserting the parent value must FAIL"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (a: int, b: int) opaque ensures a >= 0 { a := 1; b := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (a: int, b: int) opaque ensures a == 5 { a := 5; b := 6 };
}
procedure u() opaque { var o: Parent := new Child; assign var p: int, var q: int := o#m(); assert p == 1 };"},
  -- MULTI-ARG method whose ARGUMENT participates in the post: pins `restArgs` threading
  -- (self + 2 args forwarded in order) and positional Liskov param alignment over 3 inputs.
  { name := "dispatch_multiarg_in_post", outcome := .verifies,
    why := "`o#m(3, 4)` on an override `ensures r == a - b` dispatches with args forwarded IN ORDER (r == 3-4 == -1); a NON-commutative body so a swapped-arg dispatcher would give +1 and fail. Parent.post is `true` so the override refines it"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int, b: int) returns (r: int) opaque ensures true { r := 0 };
}
composite Child extends Parent {
  procedure m(self: Child, a: int, b: int) returns (r: int) opaque ensures r == a - b { r := a - b };
}
procedure u() opaque { var o: Parent := new Child; var r: int := o#m(3, 4); assert r == -1 };"},
  { name := "dispatch_through_field", outcome := .verifies,
    why := "a composite field `h#p : Parent` holding a Child dispatches to Child.m on `h#p#m()` (r==2)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
composite Holder { var p: Parent }
procedure u() opaque { var h: Holder := new Holder; h#p := new Child; var r: int := h#p#m(); assert r == 2 };"},
  -- TRANSITIVE dispatch: the overridden method is called from inside ANOTHER procedure's body
  -- (not the top-level test), so the call-site rewrite routes through the dispatcher as a
  -- non-top-level callee whose tag-conditioned posts the surrounding proof must consume.
  { name := "dispatch_transitive_call", outcome := .verifies,
    why := "`indirect(p: Parent) { r := p#m() }` called with a Child dispatches virtually inside the helper body; the helper's `ensures r >= 0` holds via the override's refined post"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure indirect(p: Parent) returns (r: int) opaque ensures r >= 0 { r := p#m() };
procedure u() opaque { var b: Parent := new Child; var r: int := indirect(b); assert r >= 0 };"},
  -- NON-OVERRIDDEN + OVERRIDDEN method coexisting in one family: `m` is overridden (gets a
  -- dispatcher + Liskov checker), `n` is not (takes the plain-lift path, no dispatcher). Both
  -- callable through a Parent-typed reference holding a Child.
  { name := "dispatch_overridden_and_non_overridden", outcome := .verifies,
    why := "in one family `m` is overridden (virtual) and `n` is not; through a Parent var holding a Child, `m` runs the override (rm==2) and `n` runs Parent's `n` (rn==9) — method-granular dispatch gate"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 1 };
  procedure n(self: Parent) returns (r: int) opaque ensures r == 9 { r := 9 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { var b: Parent := new Child; var rm: int := b#m(); var rn: int := b#n(); assert rm == 2 && rn == 9 };"},
  { name := "dispatch_reader_only", outcome := .verifies,
    why := "an overridden method that reads `self#x` into a local but writes nothing dispatches + verifies (heap-reader, not writer)"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent) returns (r: int) opaque ensures r == 0 { var t: int := self#x; r := 0 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 0 { var t: int := self#x; r := 0 };
}
procedure u() opaque { var c: Child := new Child; var b: Parent := c; var r: int := b#m(); assert r == 0 };"},
  -- The complement of `mixed_modifies_dispatch_translates` above (writer parent, neutral override).
  { name := "dispatch_reverse_mixed_modifies", outcome := .verifies,
    why := "parent `modifies c` (writer), override empty body + no modifies (neutral, narrows the frame) — under global-heap each dispatcher branch is a statement, so the mixed writer/neutral family has no `Heap`-vs-void branch join and translates + verifies"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures true modifies c { c#v := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, c: Cell) opaque ensures true { };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert 1 == 1 };"},

  -- ===== Multiple-inheritance Liskov: refinement is checked against EVERY parent =====
  -- `findOverriddenParents` (CheckOverrideRefinement) emits a checker set per parent, so a
  -- diamond override that violates the SECOND-listed parent's contract is rejected — the
  -- per-parent checker set spans all parents, not just the first-listed one a single-parent
  -- `findSome?` lookup would find.
  { name := "diamond_override_violates_second_parent_rejected", outcome := .failsExactly 1,
    why := "`C extends A, B` whose `m ensures r==5` violates B's `ensures r<=0` must be REJECTED — Liskov checks C.m against BOTH A and B, not just the first-listed parent"
    src := r"
composite A { var x: int  procedure m(self: A) returns (r: int) opaque ensures r >= 0 { r := 5 }; }
composite B { var y: int  procedure m(self: B) returns (r: int) opaque ensures r <= 0 { r := -5 }; }
composite C extends A, B { procedure m(self: C) returns (r: int) opaque ensures r == 5 { r := 5 }; }
procedure u() opaque { assert 1 == 1 };"},

  { name := "diamond_override_refines_both_parents_ok", outcome := .verifies,
    why := "positive twin: a diamond override refining BOTH parents (`ensures r==5` implies A's `r>=0` and B's `r<=10`) must still VERIFY — the all-parents check must not over-reject"
    src := r"
composite A { var x: int  procedure m(self: A) returns (r: int) opaque ensures r >= 0 { r := 5 }; }
composite B { var y: int  procedure m(self: B) returns (r: int) opaque ensures r <= 10 { r := 5 }; }
composite C extends A, B { procedure m(self: C) returns (r: int) opaque ensures r == 5 { r := 5 }; }
procedure u() opaque { assert 1 == 1 };"},

  -- ===== Dispatch families the generator cannot lower are rejected with a CLEAN diagnostic =====
  -- (not an internal StrataBug). See `validateDispatchFamilies`.
  { name := "asymmetric_throws_family_rejected", outcome := .rejectedExactly .userError,
    why := "a dispatch family where the parent method `throws` but the override does not must be REJECTED with a clean diagnostic — eliminateExceptions would otherwise heap-thread only one branch and the dispatcher's if-chain would fail to type-join (internal error)"
    src := r"
composite Err {}
composite Parent { var x: int
  procedure m(self: Parent, b: int) returns (r: int) throws (e: Err) opaque { if b == 0 then { var ex: Err := new Err; throw ex }; r := 1 };
}
composite Child extends Parent {
  procedure m(self: Child, b: int) returns (r: int) opaque ensures r == 2 { r := 2 };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "renamed_typaram_override_rejected", outcome := .rejectedExactly .userError,
    why := "a generic override that RENAMES its composite's type parameter (`SBox<U> extends Box<U>`) must be REJECTED cleanly — its `is`/`as` tag-test emits `U`, which the dispatcher's `T`-scope cannot relate (a clean diagnostic, not an internal StrataBug)"
    src := r"
composite Box<T> { var v: T
  procedure get(self: Box<T>) returns (r: T) opaque ensures true { r := self#v };
}
composite SBox<U> extends Box<U> {
  procedure get(self: SBox<U>) returns (r: U) opaque ensures true { r := self#v };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "concrete_override_of_generic_method_rejected", outcome := .rejectedExactly .userError,
    why := "a CONCRETE composite overriding a GENERIC parent's method (`IntBox extends Box<int>` with its own `get`) must be REJECTED cleanly — the generic `Box$get<T>` dispatcher's tag-test `self is IntBox` cannot be related to `Box<T>` at re-resolution (a clean diagnostic, not an internal StrataBug). Concrete composites may still INHERIT a generic parent's fields (see GenericMethodTest concrete_extends_geninst_*); only OVERRIDING its dispatched method is unsupported."
    src := r"
composite Box<T> { var v: T
  procedure get(self: Box<T>) returns (r: T) opaque ensures true { r := self#v };
}
composite IntBox extends Box<int> {
  procedure get(self: IntBox) returns (r: int) opaque ensures true { r := self#v };
}
procedure u() opaque { assert 1 == 1 };"},

  { name := "same_typaram_generic_override_ok", outcome := .verifies,
    why := "positive twin: a generic override repeating the base's type parameter verbatim (`SBox<T> extends Box<T>`) is the SUPPORTED shape and must VERIFY — the D3 rejection must only fire for renamed/concrete overrides of a generic method"
    src := r"
composite Box<T> { var v: T
  procedure get(self: Box<T>) returns (r: T) opaque ensures true { r := self#v };
}
composite SBox<T> extends Box<T> {
  procedure get(self: SBox<T>) returns (r: T) opaque ensures true { r := self#v };
}
procedure u() opaque { assert 1 == 1 };"},

  -- An input-arity difference between same-name methods across an ancestry means they are
  -- Java OVERLOADS, not an override (`Child.m()` inherits `Parent.m(int)` and adds a
  -- no-arg `m`). `sameNonSelfSignature` compares the non-`self` INPUT signature, so these
  -- are NOT a dispatch family: each lifts as its own independent method, no dispatcher is
  -- built, and both contracts verify on their own bodies — matching javac, which accepts
  -- the program.
  { name := "arity_overload_not_conflated_verifies", outcome := .verifies,
    why := "`Child.m(self)` vs `Parent.m(self, a)` are overloads (different input arity), NOT an override — no dispatch family forms, each lifts independently and verifies its own `ensures true`"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) opaque ensures true { r := a };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures true { r := 0 };
}
procedure u() opaque { assert 1 == 1 };"},

  -- TWO OVERLOADED METHODS ON ONE COMPOSITE: `Base` declares `m(self)` and `m(self, a)`.
  -- Same-composite method-name overloading is a PRE-EXISTING unsupported shape, rejected at
  -- INITIAL resolution — before dispatch/lift ever runs: instance methods are registered on
  -- the flat container-scoped key `{Type}${method}` (`containerScopedName`, no signature/
  -- overload table), so both `m`s claim `Base$m` and the second is a clean
  -- `Duplicate definition 'Base$m'` userError. (Lifting mints the SAME `Base$m` text name, so
  -- it would collide too — but resolution rejects first.) Pins that this surfaces as a clean
  -- userError, not a strata-bug. Independent of dispatch: the collision needs only the two
  -- declarations, no inheritance. NOTE: the Java frontend also refuses overloads upstream
  -- (`refuseIfOverloaded`), so no frontend emits this shape — this is a redundant backstop.
  { name := "overloaded_methods_same_composite_rejected", outcome := .rejectedExactly .userError,
    why := "`Base` declares `m(self)` and `m(self,a)`; instance methods register on the flat `Base$m` container key (no overload table), so the second is a clean `Duplicate definition` at initial resolution. Same-composite overloading is a pre-existing unsupported shape, rejected cleanly not as a strata-bug"
    src := r"
composite Base { var x: int
  procedure m(self: Base) returns (r: int) opaque ensures r >= 0 { r := 1 };
  procedure m(self: Base, a: int) returns (r: int) opaque ensures r >= 0 { r := 1 };
}
procedure u() opaque { assert 1 == 1 };"},

  -- RECEIVER-LESS (self-less) instance methods same-named across an ancestry. `sameNonSelfSignature`
  -- requires a first input (the receiver) on BOTH methods; a receiver-less method can never be
  -- virtually dispatched (no value to `self is O` tag-test), so these are NOT a dispatch family
  -- and each lifts as an independent static proc, verifying its own contract. Pins that the
  -- `inputs.drop 1` truncation does not conflate `[]`-tail methods into a family — which would
  -- make dispatcher generation emit a receiver-arg on a 0-input `$impl` (`'self' is not defined`).
  -- NOTE: a receiver-less instance method is itself a malformed shape (uncallable via `#`), but
  -- that pre-existing resolver gap is out of scope here; this only pins that dispatch does not
  -- turn it into an internal strata-bug.
  { name := "selfless_method_ancestry_not_dispatched_verifies", outcome := .verifies,
    why := "`Parent.m()` and `Child.m()` are receiver-less, so they are not a dispatch family — each lifts independently and verifies its own `ensures r >= 0`, rather than crashing dispatcher generation"
    src := r"
composite Parent { var x: int
  procedure m() returns (r: int) opaque ensures r >= 0 { r := 1 };
}
composite Child extends Parent {
  procedure m() returns (r: int) opaque ensures r >= 0 { r := 2 };
}
procedure u() opaque { assert 1 == 1 };"},

  -- Same overload shape, but the PARENT's contract references the parameter the no-arg
  -- sibling lacks (`ensures r >= a`). Because the two are NOT a family, no refinement
  -- checker is synthesized, so there is no attempt to re-express `ensures r >= a` in the
  -- no-arg method's scope (which would reference an undefined `a` and fold into an internal
  -- strata-bug). Each method verifies its own contract independently. This pins that
  -- signature-based membership keeps the arity-differing pair out of `CheckOverrideRefinement`
  -- entirely, so the strata-bug that name-conflation risked cannot arise.
  { name := "arity_overload_contract_refs_absent_param_verifies", outcome := .verifies,
    why := "parent `ensures r >= a`, no-arg sibling `ensures r >= 0`: overloads (not a family) ⇒ no synthesized checker ⇒ no reference to the absent `a`, no strata-bug; each verifies its own body"
    src := r"
composite Parent { var x: int
  procedure m(self: Parent, a: int) returns (r: int) opaque ensures r >= a { r := a };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
procedure u() opaque { assert 1 == 1 };"},

  -- An override that RENAMES a parameter its parent's `modifies` frame references. The
  -- refinement post-checker re-expresses the parent contract in the child's parameter names;
  -- the parent frame `modifies c` (parent param `c`) must be renamed to the child's `d` too,
  -- or `c` is an unresolved reference in the child-scoped checker and re-resolution fails as
  -- an internal strata-bug. This must VERIFY cleanly. (Verified: without the modifies-rename,
  -- this exact program fails with "resolution after 'CheckOverrideRefinement' … 'c' is not
  -- defined"; every other dispatch test reuses the parent's parameter names, so none exercises
  -- the rename.)
  { name := "override_renames_modifies_referenced_param", outcome := .verifies,
    why := "parent `modifies c` (param c), override renames it to `d` (`modifies d`): the parent frame is renamed into the child's names, so the checker re-resolves cleanly (no unresolved `c`, no strata-bug)"
    src := r"
composite Cell { var v: int }
composite Parent { var x: int
  procedure m(self: Parent, c: Cell) opaque ensures true modifies c { };
}
composite Child extends Parent {
  procedure m(self: Child, d: Cell) opaque ensures true modifies d { };
}
procedure u() opaque { var b: Parent := new Child; var cc: Cell := new Cell; b#m(cc); assert 1 == 1 };"},

  -- OVERLOAD-NOT-OVERRIDE (same NON-`self` param type, i.e. a genuine override) vs a true
  -- OVERLOAD (different non-`self` param type across an ancestry). Family membership is by
  -- non-`self` INPUT signature (`sameNonSelfSignature`), so these two same-name `val` methods
  -- with DIFFERENT param types (`b: BB` vs `a: AA`, `BB extends AA`) are NOT a dispatch
  -- family: no dispatcher, no Liskov pairing, each verifies its own contract. Pins that a
  -- cross-ancestry overload is not mistaken for an override — the `SubX` `val` is never forced
  -- to satisfy `BaseX.val`'s unrelated `ensures r==0`.
  { name := "overload_across_ancestry_not_dispatched_verifies", outcome := .verifies,
    why := "`BaseX.val(b:BB)` and `SubX.val(a:AA)` are OVERLOADS (different param types), not an override — not a dispatch family, so no dispatcher promises the base post on the sub branch; each verifies its own `ensures`"
    src := r"
composite AAc { }
composite BBc extends AAc { }
composite BaseXc { procedure val(self: BaseXc, b: BBc) returns (r: int) opaque ensures r == 0 { r := 0 }; }
composite SubXc extends BaseXc { procedure val(self: SubXc, a: AAc) returns (r: int) opaque ensures r == 42 { r := 42 }; }
procedure u() opaque { assert 1 == 1 };"},

  -- INCOMPATIBLE-param overload (unrelated composites `Pp`/`Qq`): as an overload it is not a
  -- dispatch family, so no dispatcher is built from the mismatched param lists and each method
  -- verifies its own contract. Pins that the incompatible-param shape stays a clean overload,
  -- never a dispatcher passing a `Pp` where the branch expects an unrelated `Qq`.
  { name := "overload_incompatible_param_types_not_dispatched_verifies", outcome := .verifies,
    why := "`BaseXf.val(b:Pp)` vs `SubXf.val(a:Qq)` (unrelated Pp/Qq) are overloads — not a family, so no dispatcher is built from mismatched param lists; no internal strata-bug, each verifies"
    src := r"
composite Pp { }
composite Qq { }
composite BaseXf { procedure val(self: BaseXf, b: Pp) returns (r: int) opaque ensures r == 0 { r := 0 }; }
composite SubXf extends BaseXf { procedure val(self: SubXf, a: Qq) returns (r: int) opaque ensures r == 0 { r := 0 }; }
procedure u() opaque { assert 1 == 1 };"},

  -- TVAR-AS-WILDCARD BOUNDARY (the subtle case). A genuine generic override that RENAMES
  -- its type parameter AND carries a non-`self` param typed by it (`Box<T>.put(x:T)` vs
  -- `SBox<U>.put(x:U)`) has non-`self` tails `[T]` vs `[U]`. A naive by-name comparison would
  -- treat `T` ≠ `U` as different signatures and silently DROP this from the family —
  -- suppressing the clean RENAMED-TYPE-PARAMS (D3) diagnostic and shipping a generic override
  -- the dispatcher cannot lower. `sameNonSelfSignature` matches a type variable on EITHER side
  -- against ANY type (`typeMatchesModuloTVars`), so `[T]`≡`[U]`, the pair STAYS a family, and
  -- D3 still rejects it cleanly. Pins that a renamed generic override stays in-family.
  { name := "renamed_typaram_override_with_tvar_param_rejected", outcome := .rejectedExactly .userError,
    why := "`SBox<U>.put(x:U)` overriding `Box<T>.put(x:T)` — type-param renamed, non-self param typed by it; tvar-as-wildcard signature match keeps it in the family so the RENAMED-TYPE-PARAMS diagnostic fires cleanly (not silently dropped as an overload)"
    src := r"
composite Box<T> { var v: T
  procedure put(self: Box<T>, x: T) returns (r: T) opaque ensures true { r := x };
}
composite SBox<U> extends Box<U> {
  procedure put(self: SBox<U>, x: U) returns (r: U) opaque ensures true { r := x };
}
procedure u() opaque { assert 1 == 1 };"},

  -- Positive twin of the boundary: the SAME shape with the type parameter kept verbatim
  -- (`SBox<T> extends Box<T>`, `put(x:T)`) is the supported generic override and must
  -- VERIFY — the wildcard match must not over-reject the same-named generic override.
  { name := "same_typaram_override_with_tvar_param_ok", outcome := .verifies,
    why := "`SBox<T>.put(x:T)` overriding `Box<T>.put(x:T)` verbatim is the supported generic override — stays in-family and dispatches, verifying at its instantiations"
    src := r"
composite Box<T> { var v: T
  procedure put(self: Box<T>, x: T) returns (r: T) opaque ensures true { r := x };
}
composite SBox<T> extends Box<T> {
  procedure put(self: SBox<T>, x: T) returns (r: T) opaque ensures true { r := x };
}
procedure u() opaque { assert 1 == 1 };"},

  -- CONCRETE OVERRIDE with a type-var-typed param — THE soundness case for tvar-as-wildcard.
  -- `IntBox extends Box<int>` overriding `Box<T>.put(x:T)` with `put(x:int)`: the base's
  -- non-`self` tail is `[T]`, the override's is `[int]`. A membership test that compared these
  -- as unequal (e.g. a type-var SENTINEL erasure, where `[$tv]` ≠ `[int]`) would EXCLUDE the
  -- override from the family, so neither D3 NOR the Liskov post-checker would run — a genuine
  -- override returning a contract-violating value (`r == 0 - 5` under the base's `r >= 0`)
  -- would then VERIFY through a `Box<int>` reference (a FALSE ACCEPT / soundness hole).
  -- Because a type var matches any type here, `[T]` matches `[int]`, the concrete override
  -- STAYS in the family, and D3 rejects it cleanly (a concrete override of a generic method
  -- is unsupported — like `concrete_override_of_generic_method_rejected`, but with a param
  -- typed by the erased var, which the empty-param `get` case does not exercise).
  { name := "concrete_override_with_tvar_param_rejected", outcome := .rejectedExactly .userError,
    why := "`IntBox extends Box<int>` overriding `Box<T>.put(x:T)` with `put(x:int)` — the concrete override must stay in the family (tvar `T` matches concrete `int`) so D3 rejects it cleanly; if it were dropped as an overload, its contract-violating body would escape both D3 and the Liskov check (false accept)"
    src := r"
composite Box<T> { var v: T
  procedure put(self: Box<T>, x: T) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite IntBox extends Box<int> {
  procedure put(self: IntBox, x: int) returns (r: int) opaque ensures r == 0 - 5 { r := 0 - 5 };
}
procedure u() opaque { assert 1 == 1 };"},

  -- EXTERNAL-IN-FAMILY guard: an `external` (body-less) base method overridden by a descendant
  -- with a real body. The dispatcher has no `$impl` to fall through to for the external base, so
  -- without the guard the lifted `T$m` stays `.External` while a receiver-passing branch call is
  -- synthesized against it → internal strata-bug. `validateDispatchFamilies` rejects the family
  -- up front with a clean userError. `.rejectedExactly` pins that only the clean diagnostic
  -- surfaces (no folded strata-bug). A non-overridden external method still lifts fine (not a
  -- family — see that external methods on composites are otherwise accepted).
  { name := "external_method_in_dispatch_family_rejected", outcome := .rejectedExactly .userError,
    why := "`BaseE.val` is `external` and `SubE` overrides it with a real body — an external endpoint has no `$impl` to dispatch, so the family is rejected cleanly rather than crashing dispatcher generation"
    src := r"
composite BaseE { procedure val(self: BaseE) returns (r: int) external; }
composite SubE extends BaseE { procedure val(self: SubE) returns (r: int) opaque ensures r == 42 { r := 42 }; }
procedure u() opaque { assert 1 == 1 };"},

  -- OUTPUT-SIGNATURE guard, COVARIANT RETURN (the sound case): an override returning a SUBTYPE
  -- of the base's return (`Dog <: Animal`) IS a lowerable, sound refinement — the base-typed
  -- output slot accepts the more-derived value, like an ordinary upcast — so the family must
  -- VERIFY, not be rejected. Pins that the output-signature guard admits covariance (a naive
  -- exact-type guard would spuriously reject this working shape).
  { name := "override_covariant_return_ok", outcome := .verifies,
    why := "`Sub.m` returns `Dog`, overriding `Base.m` returning `Animal` (Dog extends Animal) — covariant return is sound and dispatches; the output-signature guard must ADMIT it"
    src := r"
composite Animal { var a: int }
composite Dog extends Animal { var d: int }
composite Base { procedure m(self: Base) returns (r: Animal) opaque ensures true { r := new Animal }; }
composite Sub extends Base { procedure m(self: Sub) returns (r: Dog) opaque ensures true { r := new Dog }; }
procedure u() opaque { assert 1 == 1 };"},

  -- OUTPUT-SIGNATURE guard, BACKWARDS covariance (unsound narrowing): an override returning a
  -- SUPERtype (`Animal`) where the base returns `Dog` would hand a `Dog`-expecting caller an
  -- `Animal` — unsound. The output-signature guard rejects it up front with a clean userError,
  -- rather than letting the dispatcher output-assign fail at re-resolution.
  { name := "override_return_supertype_rejected", outcome := .rejectedExactly .userError,
    why := "`Sub.m` returns `Animal`, overriding `Base.m` returning `Dog` — a return SUPERtype is an unsound narrowing; rejected cleanly by the output-signature guard, not a strata-bug"
    src := r"
composite Animal2 { var a: int }
composite Dog2 extends Animal2 { var d: int }
composite Base2 { procedure m(self: Base2) returns (r: Dog2) opaque ensures true { r := new Dog2 }; }
composite Sub2 extends Base2 { procedure m(self: Sub2) returns (r: Animal2) opaque ensures true { r := new Animal2 }; }
procedure u() opaque { assert 1 == 1 };"},

  -- OUTPUT-SIGNATURE guard, UNRELATED return type: `int` overridden by `bool` — neither a
  -- subtype nor equal. The output-signature guard rejects it cleanly as a userError, rather
  -- than letting the dispatcher output-assign fail at re-resolution.
  { name := "override_return_unrelated_type_rejected", outcome := .rejectedExactly .userError,
    why := "`Sub.m` returns `bool`, overriding `Base.m` returning `int` — unrelated return type rejected cleanly by the output-signature guard, not an internal strata-bug"
    src := r"
composite BaseU { procedure m(self: BaseU) returns (r: int) opaque ensures true { r := 0 }; }
composite SubU extends BaseU { procedure m(self: SubU) returns (r: bool) opaque ensures true { r := true }; }
procedure u() opaque { assert 1 == 1 };"},

  -- OUTPUT-ARITY-MISMATCH: same non-`self` INPUT signature (so it IS a family member) but a
  -- different NUMBER of outputs. `validateDispatchFamilies`' output-signature arm rejects on
  -- the `baseM.outputs.length == ovM.outputs.length` clause up front; without it the
  -- dispatcher branch call `Sub$m$impl(self as Sub)` would assign the base's 2-output list to
  -- a 1-output impl and fold into a "call expects 2 args but 1 provided" strata-bug. Pins the
  -- arity short-circuit — the existing multi-output cases all share arity, so only this one
  -- exercises the `!=` branch.
  { name := "override_output_arity_mismatch_rejected", outcome := .rejectedExactly .userError,
    why := "`Base.m` returns `(a: int, b: int)`, `Sub.m` returns `(a: int)` — same input signature but fewer outputs; the output-signature guard rejects the family cleanly (not a strata-bug from the dispatcher branch call assigning a 2-output list to a 1-output impl)"
    src := r"
composite BaseArity { procedure m(self: BaseArity) returns (a: int, b: int) opaque ensures true { a := 0; b := 0 }; }
composite SubArity extends BaseArity { procedure m(self: SubArity) returns (a: int) opaque ensures true { a := 0 }; }
procedure u() opaque { assert 1 == 1 };"},

  -- COVARIANT return admitted by the output-signature guard, WITH A CONSTRAINING PARENT POST
  -- over the returned value (not `ensures true`). The two `override_covariant_*_return_ok`
  -- cases above use `ensures true` on both sides, so the covariance-of-return obligation is
  -- vacuous — the guard ADMITS the covariant return but nothing checks that the child's post
  -- actually re-establishes the parent's guarantee over the more-derived output. Here `Base.m`
  -- promises `r#a >= 0` on its `Animal` return and `Sub.m` (returning `Dog <: Animal`) delivers
  -- `r#a >= 0`, so the post-checker's covariance obligation over the covariant output holds and
  -- it VERIFIES. Twin below flips the child post to break it.
  { name := "override_covariant_return_constraining_post_ok", outcome := .verifies,
    why := "`Sub.m` returns `Dog` overriding `Base.m` returning `Animal` with parent post `r#a >= 0`; the child re-establishes `r#a >= 0`, so covariance-of-return over a constraining post VERIFIES (not the vacuous `ensures true` shape)"
    src := r"
composite AnimalC { var a: int }
composite DogC extends AnimalC { var d: int }
composite BaseC { procedure m(self: BaseC) returns (r: AnimalC) opaque ensures r#a >= 0 { r := new AnimalC; r#a := 1 }; }
composite SubC extends BaseC { procedure m(self: SubC) returns (r: DogC) opaque ensures r#a >= 0 { r := new DogC; r#a := 1 }; }
procedure u() opaque { assert 1 == 1 };"},

  -- MUST-FAIL twin of the above: the child's covariant `Dog` return carries a WEAKER post
  -- (`ensures true`) that does not re-establish the parent's `r#a >= 0`. The Liskov
  -- post-checker's covariance obligation must FAIL — pinning that dispatch through a
  -- covariantly-refined return value is actually contract-checked, not silently accepted once
  -- the output-signature guard admits the covariant type.
  { name := "override_covariant_return_weaker_post_rejected", outcome := .failsExactly 1,
    why := "`Sub.m` returns `Dog <: Animal` but only `ensures true`, failing to re-establish `Base.m`'s `r#a >= 0` — the covariance obligation over the covariant return FAILS (a covariant return type does not exempt the post from refinement)"
    src := r"
composite AnimalW { var a: int }
composite DogW extends AnimalW { var d: int }
composite BaseW { procedure m(self: BaseW) returns (r: AnimalW) opaque ensures r#a >= 0 { r := new AnimalW; r#a := 1 }; }
composite SubW extends BaseW { procedure m(self: SubW) returns (r: DogW) opaque ensures true { r := new DogW }; }
procedure u() opaque { assert 1 == 1 };"},

  -- Incompatible return type WHERE THE PARENT POST REFERENCES THE OUTPUT. Without the
  -- `outputSignatureCompatible` skip in `CheckOverrideRefinement.refinementCheckers`, the
  -- post-checker would re-express the parent's `ensures r >= 0` over the child's `bool`-typed
  -- `r` and fold into an internal strata-bug BEFORE the output-signature guard can reject —
  -- masking the clean userError. This is the shape the `ensures true` twins above do NOT
  -- exercise; `.rejectedExactly` pins that only the clean userError surfaces (no strata-bug).
  { name := "override_return_incompatible_post_refs_output_rejected", outcome := .rejectedExactly .userError,
    why := "`Sub.m` returns `bool` overriding `Base.m` returning `int`, and the parent post `ensures r >= 0` references the output — the refinement-checker skip keeps this a clean userError instead of a strata-bug from re-expressing `r >= 0` over a bool `r`"
    src := r"
composite BaseP { procedure m(self: BaseP) returns (r: int) opaque ensures r >= 0 { r := 0 }; }
composite SubP extends BaseP { procedure m(self: SubP) returns (r: bool) opaque ensures true { r := true }; }
procedure u() opaque { assert 1 == 1 };"},

  -- COVARIANT return where the child returns a GENERIC instantiation that extends the base's
  -- bare-composite return (`Box<int> <: Animal`, via `composite Box<T> extends Animal`). The
  -- output-signature guard peels the child's base name (`highBaseName?` on `.Applied Box<int>`
  -- → `Box`) and finds `Animal` in its ancestors, so this sound upcast VERIFIES rather than
  -- being spuriously rejected. Pins the `.Applied`-child covariant-return admission (the
  -- completeness case a `.UserDefined`-only ancestor check would have wrongly rejected).
  { name := "override_covariant_generic_return_ok", outcome := .verifies,
    why := "`Sub.m` returns `Box<int>` overriding `Base.m` returning `Animal`, where `Box<T> extends Animal` — a covariant generic-instantiation return is a sound upcast into the base slot and must VERIFY"
    src := r"
composite Animal3 { var a: int }
composite Box3<T> extends Animal3 { var v: T }
composite Base3 { procedure m(self: Base3) returns (r: Animal3) opaque ensures true { r := new Animal3 }; }
composite Sub3 extends Base3 { procedure m(self: Sub3) returns (r: Box3<int>) opaque ensures true { r := new Box3<int> }; }
procedure u() opaque { assert 1 == 1 };"},

  -- TYPE-ARGUMENT-AMBIGUOUS DIAMOND: `D<X>` inherits the generic `GBaseD`'s method through TWO
  -- parents that fix `GBaseD`'s type argument DIFFERENTLY (`MidBD → GBaseD<bool>`, `LGD<X> →
  -- GBaseD<X>`), so a `D<int>` reaches `GBaseD` at both `GBaseD<bool>` and `GBaseD<int>`. The
  -- inherited call's type argument is genuinely undetermined; `inferProcInst` REJECTS it with a
  -- clean `userError` (naming both instantiations + the disambiguating upcast), NOT the internal
  -- "'GBaseD$get' is not defined" the un-guarded ancestor pick would otherwise produce downstream.
  -- The disambiguation is available today via an upcast (`var b: GBaseD<int> := d; b#get()`), which
  -- collapses the receiver to one view — see the positive twin below.
  { name := "inherited_generic_diamond_ambiguous_type_arg_rejected", outcome := .rejectedExactly .userError,
    why := "a `D<int>` that inherits a generic parent's method through two parents fixing that parent's type arg differently (`GBaseD<bool>` vs `GBaseD<int>`) leaves the inherited call's type argument undetermined and must be REJECTED cleanly (a `userError` naming both + the upcast fix, not an internal StrataBug)"
    src := r"
composite GBaseD<T> { procedure get(self: GBaseD<T>) returns (r: T) opaque ensures true { r := r }; }
composite MidBD extends GBaseD<bool> { }
composite LGD<X> extends GBaseD<X> { }
composite D<X> extends MidBD, LGD<X> { }
procedure u() opaque { var d: D<int> := new D<int>; var g: int := d#get(); assert 1 == 1 };"},

  { name := "inherited_generic_diamond_disambiguated_by_upcast_ok", outcome := .verifies,
    why := "positive twin: upcasting the ambiguous `D<int>` to a specific `GBaseD<int>` slot collapses it to one view, so the inherited `get` binds `T := int` and VERIFIES — the disambiguation the rejection message points at"
    src := r"
composite GBaseD<T> { procedure get(self: GBaseD<T>) returns (r: T) opaque ensures true { r := r }; }
composite MidBD extends GBaseD<bool> { }
composite LGD<X> extends GBaseD<X> { }
composite D<X> extends MidBD, LGD<X> { }
procedure u() opaque { var d: D<int> := new D<int>; var b: GBaseD<int> := d; var g: int := b#get(); assert 1 == 1 };"},

  -- The ambiguous diamond reached through a POLY caller's body: `outer<S>(d: D<S>)` forwards its
  -- `d` into `innerD(d)`, so the ambiguous receiver flows through a proc that is itself cloned per
  -- instantiation. The conflict must be reported ONCE, at the concrete clone (`S := int`) — not
  -- also prematurely on `outer`'s pristine body, where `D<S>`'s ancestors are `GBaseD<bool>` vs the
  -- still-abstract `GBaseD<S>` (deferred by the concreteness gate, not a genuine conflict yet). And
  -- it must stay a clean `userError` (kind-exclusive: no internal StrataBug cascades on top). -/
  { name := "inherited_generic_diamond_through_poly_caller_rejected", outcome := .rejectedExactly .userError,
    why := "an ambiguous diamond forwarded through a poly caller's body must reject cleanly at the concrete clone with a `userError` only (the abstract-body view defers via the concreteness gate rather than reporting a premature/duplicate diagnostic)"
    src := r"
composite GBaseD2<T> { var v: T }
composite MidBD2 extends GBaseD2<bool> { }
composite LGD2<X> extends GBaseD2<X> { }
composite D2<X> extends MidBD2, LGD2<X> { }
procedure innerD<T>(p: GBaseD2<T>) returns (r: T) opaque ensures true { r := p#v };
procedure outerD<S>(d: D2<S>) returns (r: S) opaque ensures true { r := innerD(d) };
procedure u() opaque { var d: D2<int> := new D2<int>; var g: int := outerD(d); assert 1 == 1 };"},

  -- ORDER-INDEPENDENCE of the deferral: like the case above but the two CONCRETE-conflicting parents
  -- (`GBaseD3<int>`, `GBaseD3<bool>`) are listed BEFORE the abstract `LGD3<X>`. The deferral must key on
  -- the RECEIVER being abstract, not on which ancestor a search reaches first — otherwise the pristine
  -- `outerD3<S>` body would report the concrete conflict early AND the clone would report it again (a
  -- duplicate). Must reject cleanly (the exactly-once property is probe-guarded; the corpus DSL checks
  -- kind-exclusivity, not count).
  { name := "inherited_generic_diamond_concrete_conflict_before_abstract_parent_rejected", outcome := .rejectedExactly .userError,
    why := "an ambiguous diamond whose concrete-conflicting parents precede the abstract one must still reject cleanly (deferral keyed on the abstract RECEIVER, not on extends-list order, so no premature/duplicate diagnostic on the pristine poly-caller body)"
    src := r"
composite GBaseD3<T> { var v: T }
composite P1D3 extends GBaseD3<int> { }
composite P2D3 extends GBaseD3<bool> { }
composite LGD3<X> extends GBaseD3<X> { }
composite D3<X> extends P1D3, P2D3, LGD3<X> { }
procedure innerD3<T>(p: GBaseD3<T>) returns (r: T) opaque ensures true { r := p#v };
procedure outerD3<S>(d: D3<S>) returns (r: S) opaque ensures true { r := innerD3(d) };
procedure u() opaque { var d: D3<string> := new D3<string>; var g: string := outerD3(d); assert 1 == 1 };"} ]

def runDynamicDispatchTest : IO Unit := checkCases dynamicDispatchCorpus

#guard_msgs (drop info, error) in
#eval runDynamicDispatchTest
end Strata.Laurel
