/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Util.LabelGen

public section

namespace Imperative

open LabelGen (StringGenM)

/-! # `hoistLoopPrefixInits` — structured-to-structured pass (Option E)

A pass that transforms a `List (Stmt P (Cmd P))` so that every `.loop` body
contains no `.init` commands at any nesting level. Concretely, the output
satisfies `Block.loopBodyNoInits = true`.

**Option E (fresh names + substitution, sibling placement, NO wrapper).**

Strategy (post-order traversal): at every `.loop _ _ _ body _`, recurse into
`body` first (so nested loops are already hoist-processed), then call
`liftInitsInLoopBodyM` to walk the body and collect every `.init` reachable
through `.block` and `.ite` substructures (but not into nested loops, which
are already processed). For each collected init `init y ty rhs md`:

* a *fresh* name `y'` is allocated from a `StringGenState` via
  `StringGenState.gen` (injected into `P.Ident` by `HasIdent.ident`);
* a prelude havoc `init y' ty .nondet md` is emitted as a SIBLING placed
  *before* the rewritten loop (no wrapper block — the wrapper was eliminated
  by design: fresh names are hoist-only and excluded from the conclusion's
  frame, so no `projectStore`-strip is needed); and
* the loop body is rewritten by `substIdent y y'` so that every occurrence of
  `y` (including the lifted init's own `set` and any sibling references) now
  reads/writes the fresh `y'`.

Because the fresh names are produced by a single monotone `StringGenState`,
they are globally unique (`StringGenState.GenStep.subset`); in particular each
`y'` is disjoint from every source name and from every other generated name.

The pass is therefore monadic in `StringGenM = StateM StringGenState`. The
pure top-level wrapper `Block.hoistLoopPrefixInits` runs the monadic pass from
the empty state and discards the final state.

The transformation is purely structural — the preservation/postcondition
theorems are Phase 8's job (deferred under Option E: the previous same-name
postcondition proofs were stated against the old pure pass shape and are
re-derived against the monadic fresh-name pass in a later phase). This file
keeps only the pass definitions plus the shape-independent helper lemmas and
structural predicates (`allLoopBodiesInitFree`, `loopMeasureNone`) consumed by
the downstream proof files.
-/

/-- The fixed prefix used when allocating fresh hoist names. Uniqueness comes
from the underlying `StringGenState` counter, not from the prefix; the prefix
only makes generated names human-recognisable. -/
@[expose] def hoistFreshPrefix : String := "_hoist"

mutual
/-- Walk a loop body, collecting every init at any depth. For each init
`init y ty rhs md` a fresh name `y'` is generated; the prelude havoc
`init y' ty .nondet md` is harvested and the rename pair `(y, y')` recorded.
Does NOT recurse into nested `.loop` substructures (those are already
hoist-processed in post-order, so their bodies are init-free).

Returns a triple `(havocs, renames, body')`:
* `havocs` is the list of prelude commands `init y' ty .nondet md` (fresh lhs),
* `renames` is the list of `(y, y')` rename pairs to be applied to the body,
* `body'` is `s` with each lifted init rewritten as `Cmd.set y rhs md` (the
  *original* name `y`; the rename to `y'` is applied uniformly by the caller
  via `applyRenames`, so that sibling references to `y` are renamed too).

The computation threads a `StringGenState` (so it lives in `StringGenM`). -/
@[expose] def Stmt.liftInitsInLoopBodyM {P : PureExpr} [HasIdent P]
    (s : Stmt P (Cmd P)) :
    StringGenM (List (Cmd P) × List (P.Ident × P.Ident) × List (Stmt P (Cmd P))) :=
  match s with
  | .cmd (.init y ty rhs md) => fun σ =>
      let (fresh, σ') := StringGenState.gen hoistFreshPrefix σ
      let y' := HasIdent.ident fresh
      (([.init y' ty .nondet md], [(y, y')], [.cmd (.set y rhs md)]), σ')
  | .cmd c => fun σ => (([], [], [.cmd c]), σ)
  | .block lbl bss md => fun σ =>
      let ((hs, rn, bss'), σ') := Block.liftInitsInLoopBodyM bss σ
      ((hs, rn, [.block lbl bss' md]), σ')
  | .ite g tss ess md => fun σ =>
      let ((ths, trn, tss'), σ₁) := Block.liftInitsInLoopBodyM tss σ
      let ((ehs, ern, ess'), σ₂) := Block.liftInitsInLoopBodyM ess σ₁
      ((ths ++ ehs, trn ++ ern, [.ite g tss' ess' md]), σ₂)
  | .loop g m inv body md => fun σ => (([], [], [.loop g m inv body md]), σ)
  | .exit lbl md => fun σ => (([], [], [.exit lbl md]), σ)
  | .funcDecl d md => fun σ => (([], [], [.funcDecl d md]), σ)
  | .typeDecl t md => fun σ => (([], [], [.typeDecl t md]), σ)
  termination_by sizeOf s

/-- Apply `Stmt.liftInitsInLoopBodyM` to every statement in the block,
threading the `StringGenState` and concatenating the harvested havocs,
rename pairs, and rewritten residuals. -/
@[expose] def Block.liftInitsInLoopBodyM {P : PureExpr} [HasIdent P]
    (ss : List (Stmt P (Cmd P))) :
    StringGenM (List (Cmd P) × List (P.Ident × P.Ident) × List (Stmt P (Cmd P))) :=
  match ss with
  | [] => fun σ => (([], [], []), σ)
  | s :: rest => fun σ =>
      let ((hs_s, rn_s, ss_s), σ₁) := Stmt.liftInitsInLoopBodyM s σ
      let ((hs_r, rn_r, ss_r), σ₂) := Block.liftInitsInLoopBodyM rest σ₁
      ((hs_s ++ hs_r, rn_s ++ rn_r, ss_s ++ ss_r), σ₂)
  termination_by sizeOf ss
end

/-! ## Pure surface wrapper (old pair shape)

The Option-E pass is monadic and returns a TRIPLE
`(havocs, renames, residual)` inside `StringGenM`. Much downstream
structural reasoning only consumes the RESIDUAL (`.snd` in the old API)
and/or the harvested havoc prelude (`.fst` in the old API), and is agnostic
to the rename-pair component and to the concrete fresh names that the
generator produced. For those shape-only sites we expose a pure projection
`Stmt/Block.liftInitsInLoopBody` that recovers the old pair shape
`(havocs, residual)` by running the monadic pass from a FIXED initial state
(`StringGenState.emp`) and dropping the rename-pair component.

CAUTION: the `.fst` havocs are the FRESH-name havocs (`init y' ty .nondet md`
with `y'` generated from the empty state); they are NOT the source names, so
any lemma that asserts the havoc lhs lies in the source `initVars` is FALSE
under Option E and must be reformulated (output inits are fresh names, by
design). The `.snd` residual is independent of the start state (only the
fresh `.fst` names depend on it), so every shape-only postcondition over the
residual ports through the wrapper unchanged. -/

/-- Pure surface projection of `Stmt.liftInitsInLoopBodyM`: run from the empty
generator state and keep the `(havocs, residual)` pair (dropping the
rename-pair component). See the caution above on fresh `.fst` names. -/
@[expose] def Stmt.liftInitsInLoopBody {P : PureExpr} [HasIdent P]
    (s : Stmt P (Cmd P)) : List (Cmd P) × List (Stmt P (Cmd P)) :=
  let r := (Stmt.liftInitsInLoopBodyM s StringGenState.emp).1
  (r.1, r.2.2)

/-- Pure surface projection of `Block.liftInitsInLoopBodyM`: run from the
empty generator state and keep the `(havocs, residual)` pair. -/
@[expose] def Block.liftInitsInLoopBody {P : PureExpr} [HasIdent P]
    (ss : List (Stmt P (Cmd P))) : List (Cmd P) × List (Stmt P (Cmd P)) :=
  let r := (Block.liftInitsInLoopBodyM ss StringGenState.emp).1
  (r.1, r.2.2)

/-- Fold a list of `(y, y')` rename pairs over a block via `Block.substIdent`.
Because every `y'` is a fresh generated name distinct from all the `y`s and
from each other, the renames are independent of application order. -/
@[expose] def Block.applyRenames {P : PureExpr}
    [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    List (Stmt P (Cmd P)) :=
  renames.foldl (fun acc p => Block.substIdent p.1 p.2 acc) ss

mutual
/-- Top-level pass (monadic): post-order traversal threading a
`StringGenState`. For a `.loop`, recurse into the body first (so nested loops
are hoist-processed), then call `Block.liftInitsInLoopBodyM` on the
post-processed body to collect this loop's body inits with fresh names. The
fresh havocs are emitted as SIBLING commands *before* the rewritten loop, and
the body is renamed via `Block.applyRenames` so it reads/writes the fresh
names. For `.block` and `.ite`, recurse structurally. Other statements are
identity (returned as a singleton list). -/
@[expose] def Stmt.hoistLoopPrefixInitsM {P : PureExpr}
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) : StringGenM (List (Stmt P (Cmd P))) :=
  match s with
  | .cmd c => fun σ => ([.cmd c], σ)
  | .block lbl bss md => fun σ =>
      let (bss', σ') := Block.hoistLoopPrefixInitsM bss σ
      ([.block lbl bss' md], σ')
  | .ite g tss ess md => fun σ =>
      let (tss', σ₁) := Block.hoistLoopPrefixInitsM tss σ
      let (ess', σ₂) := Block.hoistLoopPrefixInitsM ess σ₁
      ([.ite g tss' ess' md], σ₂)
  | .loop g m inv body md => fun σ =>
      let (body₁, σ₁) := Block.hoistLoopPrefixInitsM body σ
      let ((havocs, renames, body₂), σ₂) := Block.liftInitsInLoopBodyM body₁ σ₁
      let body₃ := Block.applyRenames renames body₂
      (havocs.map Stmt.cmd ++ [.loop g m inv body₃ md], σ₂)
  | .exit lbl md => fun σ => ([.exit lbl md], σ)
  | .funcDecl d md => fun σ => ([.funcDecl d md], σ)
  | .typeDecl t md => fun σ => ([.typeDecl t md], σ)
  termination_by sizeOf s

/-- Apply `Stmt.hoistLoopPrefixInitsM` to each statement of the block,
threading the `StringGenState` and concatenating the resulting lists. -/
@[expose] def Block.hoistLoopPrefixInitsM {P : PureExpr}
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) : StringGenM (List (Stmt P (Cmd P))) :=
  match ss with
  | [] => fun σ => ([], σ)
  | s :: rest => fun σ =>
      let (ss_s, σ₁) := Stmt.hoistLoopPrefixInitsM s σ
      let (ss_r, σ₂) := Block.hoistLoopPrefixInitsM rest σ₁
      (ss_s ++ ss_r, σ₂)
  termination_by sizeOf ss
end

/-- Pure top-level wrapper: run the monadic fresh-name pass from the empty
`StringGenState` and discard the final state. -/
@[expose] def Block.hoistLoopPrefixInits {P : PureExpr}
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) : List (Stmt P (Cmd P)) :=
  (Block.hoistLoopPrefixInitsM ss StringGenState.emp).1

/-- Pure statement-level wrapper: run the monadic fresh-name pass from the
empty `StringGenState` and discard the final state. -/
@[expose] def Stmt.hoistLoopPrefixInits {P : PureExpr}
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) : List (Stmt P (Cmd P)) :=
  (Stmt.hoistLoopPrefixInitsM s StringGenState.emp).1

/-! ## Shape-independent helper lemmas

These distribute the structural Bool walkers over `++` and assert their
triviality on `.cmd`-only prelude lists. They do not mention the hoist pass
itself, so they survive the Option E pass rewrite unchanged and are consumed
by the downstream proof files. -/

/-- Concatenation distributes over `Block.initVars`. -/
private theorem Block.initVars_append {P : PureExpr}
    (xs ys : List (Stmt P (Cmd P))) :
    Block.initVars (xs ++ ys) = Block.initVars xs ++ Block.initVars ys := by
  induction xs with
  | nil => simp [Block.initVars]
  | cons x rest ih =>
    simp [ih, List.append_assoc]

/-! ## Phase 8 §E5 (Option A): strengthened structural predicate

`Block.allLoopBodiesInitFree` mirrors `Block.loopBodyNoInits` but uses
`Block.noInitsAnywhere` at the `.loop` arm instead of just
`(Block.initVars _).isEmpty`, capturing that every `.loop` body contains no
`.init` commands at ANY nesting depth (including inside `.block` and `.ite`
substructures of the loop body). The postcondition that the pass output
satisfies this predicate is deferred (re-derived against the monadic
fresh-name pass in a later phase). -/

mutual
/-- Returns true if every `.loop` body in `s` contains no `.init` commands
at any nesting depth. Recurses through `.ite`, `.block`, and `.loop` to
enforce the restriction at every loop nesting level. -/
@[expose] def Stmt.allLoopBodiesInitFree {P : PureExpr}
    (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.allLoopBodiesInitFree bss
  | .ite _ tss ess _ =>
      Block.allLoopBodiesInitFree tss && Block.allLoopBodiesInitFree ess
  | .loop _ _ _ bss _ =>
      Block.noInitsAnywhere bss && Block.allLoopBodiesInitFree bss
  | .exit _ _ => true
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by sizeOf s

/-- Returns true if every `.loop` body in `ss` contains no `.init` commands
at any nesting depth. -/
@[expose] def Block.allLoopBodiesInitFree {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: srest =>
      Stmt.allLoopBodiesInitFree s && Block.allLoopBodiesInitFree srest
  termination_by sizeOf ss
end

/-- Concatenation distributes over `Block.allLoopBodiesInitFree`. -/
private theorem Block.allLoopBodiesInitFree_append {P : PureExpr}
    (xs ys : List (Stmt P (Cmd P))) :
    Block.allLoopBodiesInitFree (xs ++ ys) =
      (Block.allLoopBodiesInitFree xs && Block.allLoopBodiesInitFree ys) := by
  induction xs with
  | nil => simp [Block.allLoopBodiesInitFree]
  | cons x rest ih =>
    simp [Block.allLoopBodiesInitFree, ih, Bool.and_assoc]

/-- Concatenation distributes over `Block.noInitsAnywhere`. -/
private theorem Block.noInitsAnywhere_append {P : PureExpr}
    (xs ys : List (Stmt P (Cmd P))) :
    Block.noInitsAnywhere (xs ++ ys) =
      (Block.noInitsAnywhere xs && Block.noInitsAnywhere ys) := by
  induction xs with
  | nil => simp [Block.noInitsAnywhere]
  | cons x rest ih =>
    simp [Block.noInitsAnywhere, ih, Bool.and_assoc]

/-- A list of non-init `.cmd`s contributes trivially to
`Block.allLoopBodiesInitFree`. -/
private theorem Block.allLoopBodiesInitFree_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.allLoopBodiesInitFree (cs.map Stmt.cmd) = true := by
  induction cs with
  | nil => simp [Block.allLoopBodiesInitFree]
  | cons c rest ih =>
    simp [List.map_cons, Block.allLoopBodiesInitFree,
          Stmt.allLoopBodiesInitFree, ih]

/-! ## Phase 8 §B: `loopMeasureNone` predicate

A boolean walker that asserts `m.isNone` at every `.loop` node and recurses
through every structural substructure (`.block`, `.ite`, `.loop` body).
Programs carrying explicit termination measures are out of scope for the
hoisting pass's correctness statement until measure-aware variants land in
Phase 9. -/

mutual
/-- Returns true if every `.loop` in `s` (and any nested loop) has
`measure = none`. -/
@[expose] def Stmt.loopMeasureNone {P : PureExpr} (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.loopMeasureNone bss
  | .ite _ tss ess _ => Block.loopMeasureNone tss && Block.loopMeasureNone ess
  | .loop _ m _ bss _ => m.isNone && Block.loopMeasureNone bss
  | .exit _ _ => true
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by sizeOf s

/-- Returns true if every `.loop` in `ss` (and any nested loops) has
`measure = none`. -/
@[expose] def Block.loopMeasureNone {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: srest => Stmt.loopMeasureNone s && Block.loopMeasureNone srest
  termination_by sizeOf ss
end

/-- `Block.loopMeasureNone` distributes over `++`. -/
private theorem Block.loopMeasureNone_append {P : PureExpr}
    (xs ys : List (Stmt P (Cmd P))) :
    Block.loopMeasureNone (xs ++ ys) =
      (Block.loopMeasureNone xs && Block.loopMeasureNone ys) := by
  induction xs with
  | nil => simp [Block.loopMeasureNone]
  | cons x rest ih =>
    simp [Block.loopMeasureNone, ih, Bool.and_assoc]

/-- A list of `.cmd`s trivially has `loopMeasureNone = true`. -/
private theorem Block.loopMeasureNone_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.loopMeasureNone (cs.map Stmt.cmd) = true := by
  induction cs with
  | nil => simp [Block.loopMeasureNone]
  | cons c rest ih =>
    simp [List.map_cons, Block.loopMeasureNone, Stmt.loopMeasureNone, ih]

/-- `Block.simpleShape` distributes over `++`. -/
private theorem Block.simpleShape_append {P : PureExpr}
    (xs ys : List (Stmt P (Cmd P))) :
    Block.simpleShape (xs ++ ys) =
      (Block.simpleShape xs && Block.simpleShape ys) := by
  induction xs with
  | nil => simp [Block.simpleShape]
  | cons x rest ih =>
    simp [Block.simpleShape, ih, Bool.and_assoc]

/-- A list of `.cmd`s trivially has `simpleShape = true`. -/
private theorem Block.simpleShape_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.simpleShape (cs.map Stmt.cmd) = true := by
  induction cs with
  | nil => simp [Block.simpleShape]
  | cons c rest ih =>
    simp [List.map_cons, Block.simpleShape, Stmt.simpleShape, ih]

/-- `Block.containsNondetLoop` distributes over `++`. -/
private theorem Block.containsNondetLoop_append {P : PureExpr}
    (xs ys : List (Stmt P (Cmd P))) :
    Block.containsNondetLoop (xs ++ ys) =
      (Block.containsNondetLoop xs || Block.containsNondetLoop ys) := by
  induction xs with
  | nil => simp [Block.containsNondetLoop]
  | cons x rest ih => simp [Block.containsNondetLoop, ih, Bool.or_assoc]

/-- A list of `.cmd`s never contains a nondet loop. -/
private theorem Block.containsNondetLoop_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.containsNondetLoop (cs.map Stmt.cmd) = false := by
  induction cs with
  | nil => simp [Block.containsNondetLoop]
  | cons c rest ih =>
    simp [List.map_cons, Block.containsNondetLoop, Stmt.containsNondetLoop, ih]

/-- `Block.containsFuncDecl` distributes over `++`. -/
private theorem Block.containsFuncDecl_append {P : PureExpr}
    (xs ys : List (Stmt P (Cmd P))) :
    Block.containsFuncDecl (xs ++ ys) =
      (Block.containsFuncDecl xs || Block.containsFuncDecl ys) := by
  induction xs with
  | nil => simp [Block.containsFuncDecl]
  | cons x rest ih => simp [Block.containsFuncDecl, ih, Bool.or_assoc]

/-- A list of `.cmd`s never contains a funcDecl. -/
private theorem Block.containsFuncDecl_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.containsFuncDecl (cs.map Stmt.cmd) = false := by
  induction cs with
  | nil => simp [Block.containsFuncDecl]
  | cons c rest ih =>
    simp [List.map_cons, Block.containsFuncDecl, Stmt.containsFuncDecl, ih]

/-- `Block.loopHasNoInvariants` distributes over `++`. -/
private theorem Block.loopHasNoInvariants_append {P : PureExpr}
    (xs ys : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (xs ++ ys) =
      (Block.loopHasNoInvariants xs && Block.loopHasNoInvariants ys) := by
  induction xs with
  | nil => simp [Block.loopHasNoInvariants]
  | cons x rest ih => simp [Block.loopHasNoInvariants, ih, Bool.and_assoc]

/-- A list of `.cmd`s trivially has `loopHasNoInvariants = true`. -/
private theorem Block.loopHasNoInvariants_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.loopHasNoInvariants (cs.map Stmt.cmd : List (Stmt P (Cmd P))) = true := by
  induction cs with
  | nil => simp [Block.loopHasNoInvariants]
  | cons c rest ih =>
    simp [List.map_cons, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, ih]

/-! ## `substIdent` / `applyRenames` preserve the structural Bool predicates

`Block.substIdent y y'` only renames identifiers; it never changes the
statement TREE shape (`.cmd`/`.block`/`.ite`/`.loop` stay put, `.init` stays
`.init` and `.set` stays `.set`). Consequently every structural Bool walker
that inspects only the tree shape (`loopBodyNoInits`, `noInitsAnywhere`,
`allLoopBodiesInitFree`, `loopMeasureNone`) is invariant under a rename, and
hence under `Block.applyRenames` (a fold of renames). `Block.initVars` is the
one walker that *does* track names: a rename preserves its LENGTH (each
`.init` lhs maps to exactly one new name), which is enough to preserve the
`(Block.initVars _).isEmpty` test used inside `loopBodyNoInits`. -/

section SubstIdentPreserves
variable {P : PureExpr} [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]

mutual
/-- `Stmt.substIdent` preserves the LENGTH of `initVars` (a rename maps each
`.init` lhs to exactly one new name). -/
theorem Stmt.substIdent_initVars_length (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    (Stmt.initVars (Stmt.substIdent y y' s)).length = (Stmt.initVars s).length := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.initVars]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.initVars_block]
      exact Block.substIdent_initVars_length y y' bss
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.initVars_ite, List.length_append]
      rw [Block.substIdent_initVars_length y y' tss,
          Block.substIdent_initVars_length y y' ess]
  | .loop g m inv bss md =>
      simp only [Stmt.substIdent_loop, Stmt.initVars_loop]
      exact Block.substIdent_initVars_length y y' bss
  | .exit lbl md => simp [Stmt.initVars]
  | .funcDecl d md => simp [Stmt.initVars]
  | .typeDecl t md => simp [Stmt.initVars]
  termination_by sizeOf s

theorem Block.substIdent_initVars_length (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    (Block.initVars (Block.substIdent y y' ss)).length = (Block.initVars ss).length := by
  match ss with
  | [] => simp [Block.initVars]
  | s :: rest =>
      simp only [Block.substIdent, Block.initVars_cons, List.length_append]
      rw [Stmt.substIdent_initVars_length y y' s,
          Block.substIdent_initVars_length y y' rest]
  termination_by sizeOf ss
end

/-- `isEmpty` of `initVars` is invariant under a rename (via length). -/
theorem Block.substIdent_initVars_isEmpty (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    (Block.initVars (Block.substIdent y y' ss)).isEmpty
      = (Block.initVars ss).isEmpty := by
  have hlen := Block.substIdent_initVars_length y y' ss
  cases h₁ : Block.initVars (Block.substIdent y y' ss) <;>
    cases h₂ : Block.initVars ss <;>
    simp_all [List.isEmpty]

mutual
/-- `Stmt.substIdent` preserves `noInitsAnywhere`. -/
theorem Stmt.substIdent_noInitsAnywhere (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    Stmt.noInitsAnywhere (Stmt.substIdent y y' s) = Stmt.noInitsAnywhere s := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.noInitsAnywhere]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.noInitsAnywhere]
      exact Block.substIdent_noInitsAnywhere y y' bss
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.noInitsAnywhere]
      rw [Block.substIdent_noInitsAnywhere y y' tss,
          Block.substIdent_noInitsAnywhere y y' ess]
  | .loop g m inv bss md =>
      simp only [Stmt.substIdent_loop, Stmt.noInitsAnywhere]
      exact Block.substIdent_noInitsAnywhere y y' bss
  | .exit lbl md => simp [Stmt.noInitsAnywhere]
  | .funcDecl d md => simp [Stmt.noInitsAnywhere]
  | .typeDecl t md => simp [Stmt.noInitsAnywhere]
  termination_by sizeOf s

theorem Block.substIdent_noInitsAnywhere (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    Block.noInitsAnywhere (Block.substIdent y y' ss) = Block.noInitsAnywhere ss := by
  match ss with
  | [] => simp [Block.noInitsAnywhere]
  | s :: rest =>
      simp only [Block.substIdent, Block.noInitsAnywhere]
      rw [Stmt.substIdent_noInitsAnywhere y y' s,
          Block.substIdent_noInitsAnywhere y y' rest]
  termination_by sizeOf ss
end

mutual
/-- `Stmt.substIdent` preserves `allLoopBodiesInitFree`. -/
theorem Stmt.substIdent_allLoopBodiesInitFree (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    Stmt.allLoopBodiesInitFree (Stmt.substIdent y y' s)
      = Stmt.allLoopBodiesInitFree s := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.allLoopBodiesInitFree]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.allLoopBodiesInitFree]
      exact Block.substIdent_allLoopBodiesInitFree y y' bss
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.allLoopBodiesInitFree]
      rw [Block.substIdent_allLoopBodiesInitFree y y' tss,
          Block.substIdent_allLoopBodiesInitFree y y' ess]
  | .loop g m inv bss md =>
      simp only [Stmt.substIdent_loop, Stmt.allLoopBodiesInitFree]
      rw [Block.substIdent_noInitsAnywhere y y' bss,
          Block.substIdent_allLoopBodiesInitFree y y' bss]
  | .exit lbl md => simp [Stmt.allLoopBodiesInitFree]
  | .funcDecl d md => simp [Stmt.allLoopBodiesInitFree]
  | .typeDecl t md => simp [Stmt.allLoopBodiesInitFree]
  termination_by sizeOf s

theorem Block.substIdent_allLoopBodiesInitFree (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    Block.allLoopBodiesInitFree (Block.substIdent y y' ss)
      = Block.allLoopBodiesInitFree ss := by
  match ss with
  | [] => simp [Block.allLoopBodiesInitFree]
  | s :: rest =>
      simp only [Block.substIdent, Block.allLoopBodiesInitFree]
      rw [Stmt.substIdent_allLoopBodiesInitFree y y' s,
          Block.substIdent_allLoopBodiesInitFree y y' rest]
  termination_by sizeOf ss
end

mutual
/-- `Stmt.substIdent` preserves `loopMeasureNone` (a rename maps `m` via
`Option.map`, so `m.isNone` is unchanged). -/
theorem Stmt.substIdent_loopMeasureNone (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    Stmt.loopMeasureNone (Stmt.substIdent y y' s) = Stmt.loopMeasureNone s := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.loopMeasureNone]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.loopMeasureNone]
      exact Block.substIdent_loopMeasureNone y y' bss
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.loopMeasureNone]
      rw [Block.substIdent_loopMeasureNone y y' tss,
          Block.substIdent_loopMeasureNone y y' ess]
  | .loop g m inv bss md =>
      simp only [Stmt.substIdent_loop, Stmt.loopMeasureNone, Option.isNone_map]
      rw [Block.substIdent_loopMeasureNone y y' bss]
  | .exit lbl md => simp [Stmt.loopMeasureNone]
  | .funcDecl d md => simp [Stmt.loopMeasureNone]
  | .typeDecl t md => simp [Stmt.loopMeasureNone]
  termination_by sizeOf s

theorem Block.substIdent_loopMeasureNone (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    Block.loopMeasureNone (Block.substIdent y y' ss) = Block.loopMeasureNone ss := by
  match ss with
  | [] => simp [Block.loopMeasureNone]
  | s :: rest =>
      simp only [Block.substIdent, Block.loopMeasureNone]
      rw [Stmt.substIdent_loopMeasureNone y y' s,
          Block.substIdent_loopMeasureNone y y' rest]
  termination_by sizeOf ss
end

/-! ### Lift `substIdent`-invariance through `applyRenames` (a fold of renames) -/

/-- `Block.applyRenames` preserves `noInitsAnywhere`. -/
theorem Block.applyRenames_noInitsAnywhere
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.noInitsAnywhere (Block.applyRenames renames ss)
      = Block.noInitsAnywhere ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_noInitsAnywhere]

/-- `Block.applyRenames` preserves `allLoopBodiesInitFree`. -/
theorem Block.applyRenames_allLoopBodiesInitFree
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.allLoopBodiesInitFree (Block.applyRenames renames ss)
      = Block.allLoopBodiesInitFree ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_allLoopBodiesInitFree]

/-- `Block.applyRenames` preserves `loopMeasureNone`. -/
theorem Block.applyRenames_loopMeasureNone
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.loopMeasureNone (Block.applyRenames renames ss)
      = Block.loopMeasureNone ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_loopMeasureNone]

/-! ### `substIdent` / `applyRenames` preserve `simpleShape`

`simpleShape` is a shape-only walker: it only inspects whether a guard is
`.det`/`.nondet`.  A rename maps a `.det e` guard to `.det (substFvar …)` —
still `.det` — and recurses structurally, so the shape characteristic is
unchanged.  These mirror the `loopMeasureNone` preservation chain above and
feed the `simpleShape`-preservation of the whole hoisting pass. -/

mutual
/-- `Stmt.substIdent` preserves `simpleShape`. -/
theorem Stmt.substIdent_simpleShape (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    Stmt.simpleShape (Stmt.substIdent y y' s) = Stmt.simpleShape s := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.simpleShape]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.simpleShape]
      exact Block.substIdent_simpleShape y y' bss
  | .ite (.det e) tss ess md =>
      simp only [Stmt.substIdent_ite, ExprOrNondet.substIdent_det, Stmt.simpleShape]
      rw [Block.substIdent_simpleShape y y' tss,
          Block.substIdent_simpleShape y y' ess]
  | .ite .nondet tss ess md =>
      simp only [Stmt.substIdent_ite, ExprOrNondet.substIdent_nondet, Stmt.simpleShape]
  | .loop (.det e) m inv bss md =>
      simp only [Stmt.substIdent_loop, ExprOrNondet.substIdent_det, Stmt.simpleShape]
      rw [Block.substIdent_simpleShape y y' bss]
  | .loop .nondet m inv bss md =>
      simp only [Stmt.substIdent_loop, ExprOrNondet.substIdent_nondet, Stmt.simpleShape]
      rw [Block.substIdent_simpleShape y y' bss]
  | .exit lbl md => simp [Stmt.simpleShape]
  | .funcDecl d md => simp [Stmt.simpleShape]
  | .typeDecl t md => simp [Stmt.simpleShape]
  termination_by sizeOf s

theorem Block.substIdent_simpleShape (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    Block.simpleShape (Block.substIdent y y' ss) = Block.simpleShape ss := by
  match ss with
  | [] => simp [Block.simpleShape]
  | s :: rest =>
      simp only [Block.substIdent, Block.simpleShape]
      rw [Stmt.substIdent_simpleShape y y' s,
          Block.substIdent_simpleShape y y' rest]
  termination_by sizeOf ss
end

/-- `Block.applyRenames` preserves `simpleShape`. -/
theorem Block.applyRenames_simpleShape
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.simpleShape (Block.applyRenames renames ss)
      = Block.simpleShape ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_simpleShape]

/-! ### `substIdent` / `applyRenames` preserve `containsNondetLoop`,
`containsFuncDecl`, `loopHasNoInvariants`

All three are shape-only walkers. A rename keeps a `.loop` guard's `.det`/
`.nondet` shape (`containsNondetLoop`), keeps `.funcDecl` constructors
(`containsFuncDecl`), and maps a loop's invariant list by `.map`, preserving
its length and hence `inv.isEmpty` (`loopHasNoInvariants`). -/

mutual
theorem Stmt.substIdent_containsNondetLoop (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    Stmt.containsNondetLoop (Stmt.substIdent y y' s) = Stmt.containsNondetLoop s := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.containsNondetLoop]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.containsNondetLoop]
      exact Block.substIdent_containsNondetLoop y y' bss
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.containsNondetLoop]
      rw [Block.substIdent_containsNondetLoop y y' tss,
          Block.substIdent_containsNondetLoop y y' ess]
  | .loop g m inv bss md =>
      cases g <;>
        simp [Stmt.substIdent_loop, Stmt.containsNondetLoop, ExprOrNondet.substIdent,
              Block.substIdent_containsNondetLoop y y' bss]
  | .exit lbl md => simp [Stmt.containsNondetLoop]
  | .funcDecl d md => simp [Stmt.containsNondetLoop]
  | .typeDecl t md => simp [Stmt.containsNondetLoop]
  termination_by sizeOf s

theorem Block.substIdent_containsNondetLoop (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    Block.containsNondetLoop (Block.substIdent y y' ss) = Block.containsNondetLoop ss := by
  match ss with
  | [] => simp [Block.containsNondetLoop]
  | s :: rest =>
      simp only [Block.substIdent, Block.containsNondetLoop]
      rw [Stmt.substIdent_containsNondetLoop y y' s,
          Block.substIdent_containsNondetLoop y y' rest]
  termination_by sizeOf ss
end

mutual
theorem Stmt.substIdent_containsFuncDecl (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    Stmt.containsFuncDecl (Stmt.substIdent y y' s) = Stmt.containsFuncDecl s := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.containsFuncDecl]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.containsFuncDecl]
      exact Block.substIdent_containsFuncDecl y y' bss
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.containsFuncDecl]
      rw [Block.substIdent_containsFuncDecl y y' tss,
          Block.substIdent_containsFuncDecl y y' ess]
  | .loop g m inv bss md =>
      simp only [Stmt.substIdent_loop, Stmt.containsFuncDecl]
      exact Block.substIdent_containsFuncDecl y y' bss
  | .exit lbl md => simp [Stmt.containsFuncDecl]
  | .funcDecl d md => simp [Stmt.containsFuncDecl]
  | .typeDecl t md => simp [Stmt.containsFuncDecl]
  termination_by sizeOf s

theorem Block.substIdent_containsFuncDecl (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    Block.containsFuncDecl (Block.substIdent y y' ss) = Block.containsFuncDecl ss := by
  match ss with
  | [] => simp [Block.containsFuncDecl]
  | s :: rest =>
      simp only [Block.substIdent, Block.containsFuncDecl]
      rw [Stmt.substIdent_containsFuncDecl y y' s,
          Block.substIdent_containsFuncDecl y y' rest]
  termination_by sizeOf ss
end

mutual
theorem Stmt.substIdent_loopHasNoInvariants (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    Stmt.loopHasNoInvariants (Stmt.substIdent y y' s) = Stmt.loopHasNoInvariants s := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.loopHasNoInvariants]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.loopHasNoInvariants]
      exact Block.substIdent_loopHasNoInvariants y y' bss
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.loopHasNoInvariants]
      rw [Block.substIdent_loopHasNoInvariants y y' tss,
          Block.substIdent_loopHasNoInvariants y y' ess]
  | .loop g m inv bss md =>
      simp only [Stmt.substIdent_loop, Stmt.loopHasNoInvariants, List.isEmpty_map]
      rw [Block.substIdent_loopHasNoInvariants y y' bss]
  | .exit lbl md => simp [Stmt.loopHasNoInvariants]
  | .funcDecl d md => simp [Stmt.loopHasNoInvariants]
  | .typeDecl t md => simp [Stmt.loopHasNoInvariants]
  termination_by sizeOf s

theorem Block.substIdent_loopHasNoInvariants (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (Block.substIdent y y' ss) = Block.loopHasNoInvariants ss := by
  match ss with
  | [] => simp [Block.loopHasNoInvariants]
  | s :: rest =>
      simp only [Block.substIdent, Block.loopHasNoInvariants]
      rw [Stmt.substIdent_loopHasNoInvariants y y' s,
          Block.substIdent_loopHasNoInvariants y y' rest]
  termination_by sizeOf ss
end

/-- `Block.applyRenames` preserves `containsNondetLoop`. -/
theorem Block.applyRenames_containsNondetLoop
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.containsNondetLoop (Block.applyRenames renames ss)
      = Block.containsNondetLoop ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_containsNondetLoop]

/-- `Block.applyRenames` preserves `containsFuncDecl`. -/
theorem Block.applyRenames_containsFuncDecl
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.containsFuncDecl (Block.applyRenames renames ss)
      = Block.containsFuncDecl ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_containsFuncDecl]

/-- `Block.applyRenames` preserves `loopHasNoInvariants`. -/
theorem Block.applyRenames_loopHasNoInvariants
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (Block.applyRenames renames ss)
      = Block.loopHasNoInvariants ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_loopHasNoInvariants]

end SubstIdentPreserves

/-! ## Structural postconditions of the monadic fresh-name pass

The three structural Bool walkers (`allLoopBodiesInitFree`, `loopBodyNoInits`,
`loopMeasureNone`) are reproven against the monadic pass shape. The residual
projection `(... σ).1.2.2` of `liftInitsInLoopBodyM` plays the role of the old
`.snd`; the harvested havoc prelude `(... σ).1.1` is a list of `.cmd .init`
commands (handled by the `_map_cmd` helper lemmas); the rename list
`(... σ).1.2.1` only matters for the final `applyRenames` step, which is
invariant for every structural Bool walker (see `SubstIdentPreserves`).

Because none of these walkers inspect identifier *names* (only the tree
shape), every lemma generalises over the threaded `StringGenState σ`. -/

section MonadicPostconds
variable {P : PureExpr} [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]

/-! ### Residual-projection (`.1.2.2`) equations for the lift

The monadic `liftInitsInLoopBodyM` arms destructure the recursive call with a
`let ((hs, rn, ss'), σ') := …` pattern; the projections below extract the
residual `.1.2.2` per-constructor so the structural proofs can `rw` against
the recursive residual without unfolding the whole `let`. -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
private theorem Stmt.liftInitsInLoopBodyM_block_residual
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM (.block lbl bss md) σ).1.2.2 =
      [Stmt.block lbl (Block.liftInitsInLoopBodyM bss σ).1.2.2 md] := by
  rw [Stmt.liftInitsInLoopBodyM]
  rcases h : Block.liftInitsInLoopBodyM bss σ with ⟨⟨hs, rn, bss'⟩, σ'⟩
  simp only [h]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
private theorem Stmt.liftInitsInLoopBodyM_ite_residual
    (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM (.ite g tss ess md) σ).1.2.2 =
      [Stmt.ite g (Block.liftInitsInLoopBodyM tss σ).1.2.2
                  (Block.liftInitsInLoopBodyM ess
                    (Block.liftInitsInLoopBodyM tss σ).2).1.2.2 md] := by
  rw [Stmt.liftInitsInLoopBodyM]
  rcases h₁ : Block.liftInitsInLoopBodyM tss σ with ⟨⟨ths, trn, tss'⟩, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM ess σ₁ with ⟨⟨ehs, ern, ess'⟩, σ₂⟩
  simp only [h₁, h₂]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
private theorem Block.liftInitsInLoopBodyM_cons_residual
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.liftInitsInLoopBodyM (s :: rest) σ).1.2.2 =
      (Stmt.liftInitsInLoopBodyM s σ).1.2.2 ++
        (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).1.2.2 := by
  rw [Block.liftInitsInLoopBodyM]
  rcases h₁ : Stmt.liftInitsInLoopBodyM s σ with ⟨⟨hs_s, rn_s, ss_s⟩, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM rest σ₁ with ⟨⟨hs_r, rn_r, ss_r⟩, σ₂⟩
  simp only [h₁, h₂]

/-! ### State-independence of the residual

The residual component (`.1.2.2`) of the monadic lift only ever rewrites
`init` to `set` (same name) and recurses structurally; it never reads the
generator state (only the FRESH `.fst` havoc names do). Hence the residual is
independent of the start state, and in particular equals the residual run
from `StringGenState.emp` — i.e. `(liftInitsInLoopBody _).snd`. This is the
bridge that lets every shape-only postcondition the pass proves over
`(... σ).1.2.2` port to the pure wrapper. -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
/-- The residual of `Stmt.liftInitsInLoopBodyM s σ` is independent of `σ`. -/
private theorem Stmt.liftInitsInLoopBodyM_snd_state_indep
    (s : Stmt P (Cmd P)) (σ σ' : StringGenState) :
    (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      (Stmt.liftInitsInLoopBodyM s σ').1.2.2 := by
  match s with
  | .cmd c =>
      cases c <;> simp [Stmt.liftInitsInLoopBodyM]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual,
          Stmt.liftInitsInLoopBodyM_block_residual]
      rw [Block.liftInitsInLoopBodyM_snd_state_indep bss σ σ']
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual,
          Stmt.liftInitsInLoopBodyM_ite_residual]
      rw [Block.liftInitsInLoopBodyM_snd_state_indep tss σ σ',
          Block.liftInitsInLoopBodyM_snd_state_indep ess _ _]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBodyM]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM]
  termination_by sizeOf s

/-- The residual of `Block.liftInitsInLoopBodyM ss σ` is independent of `σ`. -/
private theorem Block.liftInitsInLoopBodyM_snd_state_indep
    (ss : List (Stmt P (Cmd P))) (σ σ' : StringGenState) :
    (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      (Block.liftInitsInLoopBodyM ss σ').1.2.2 := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual,
          Block.liftInitsInLoopBodyM_cons_residual]
      rw [Stmt.liftInitsInLoopBodyM_snd_state_indep s σ σ',
          Block.liftInitsInLoopBodyM_snd_state_indep rest _ _]
  termination_by sizeOf ss
end

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
/-- The pure wrapper's residual equals the monadic residual at any state. -/
theorem Stmt.liftInitsInLoopBody_snd_eq
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (Stmt.liftInitsInLoopBody s).snd = (Stmt.liftInitsInLoopBodyM s σ).1.2.2 := by
  rw [Stmt.liftInitsInLoopBody]
  exact Stmt.liftInitsInLoopBodyM_snd_state_indep s StringGenState.emp σ

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
/-- The pure wrapper's residual equals the monadic residual at any state. -/
theorem Block.liftInitsInLoopBody_snd_eq
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.liftInitsInLoopBody ss).snd = (Block.liftInitsInLoopBodyM ss σ).1.2.2 := by
  rw [Block.liftInitsInLoopBody]
  exact Block.liftInitsInLoopBodyM_snd_state_indep ss StringGenState.emp σ

/-! ### Identity of the lift output when `initVars = []`

When the input has no `init` anywhere shallowly (`Stmt.initVars`/`Block.initVars
= []`), the fresh-name generator never fires: the harvested havoc prelude is
empty (`.1.1 = []`), the rename list is empty (`.1.2.1 = []`), and the residual
is the input verbatim (`.1.2.2 = [s]` / `= ss`). Because no fresh name is ever
generated, the whole `.1` triple is independent of `σ`. This is a shape-only
fact (it never inspects names) and ports the pure-wrapper `_no_inits` lemma in
`LoopInitHoistRewrite.lean`. -/

/-! #### Harvest-projection (`.1.1`) equations for the lift

Companion to the residual (`.1.2.2`) equations above: these extract the
harvested havoc prelude `.1.1` per-constructor so the `_no_inits` `.1.1 = []`
proofs can `rw` against the recursive sub-harvests without unfolding the `let`. -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
private theorem Stmt.liftInitsInLoopBodyM_block_harvest
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM (.block lbl bss md) σ).1.1 =
      (Block.liftInitsInLoopBodyM bss σ).1.1 := by
  rw [Stmt.liftInitsInLoopBodyM]
  rcases h : Block.liftInitsInLoopBodyM bss σ with ⟨⟨hs, rn, bss'⟩, σ'⟩
  simp only [h]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
private theorem Stmt.liftInitsInLoopBodyM_ite_harvest
    (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM (.ite g tss ess md) σ).1.1 =
      (Block.liftInitsInLoopBodyM tss σ).1.1 ++
        (Block.liftInitsInLoopBodyM ess
          (Block.liftInitsInLoopBodyM tss σ).2).1.1 := by
  rw [Stmt.liftInitsInLoopBodyM]
  rcases h₁ : Block.liftInitsInLoopBodyM tss σ with ⟨⟨ths, trn, tss'⟩, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM ess σ₁ with ⟨⟨ehs, ern, ess'⟩, σ₂⟩
  simp only [h₁, h₂]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
private theorem Block.liftInitsInLoopBodyM_cons_harvest
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.liftInitsInLoopBodyM (s :: rest) σ).1.1 =
      (Stmt.liftInitsInLoopBodyM s σ).1.1 ++
        (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).1.1 := by
  rw [Block.liftInitsInLoopBodyM]
  rcases h₁ : Stmt.liftInitsInLoopBodyM s σ with ⟨⟨hs_s, rn_s, ss_s⟩, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM rest σ₁ with ⟨⟨hs_r, rn_r, ss_r⟩, σ₂⟩
  simp only [h₁, h₂]

/-! #### `_no_inits`: harvest is empty and residual is the identity

Under `initVars = []` the harvest (`.1.1`) is empty and the residual
(`.1.2.2`) is the input verbatim. Both facts are shape-only (no name is read),
so they hold at any `σ` and port to the pure wrapper. -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
/-- Under `Stmt.initVars s = []`, the harvested havoc prelude is empty. -/
private theorem Stmt.liftInitsInLoopBodyM_fst_no_inits
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h_iv : Stmt.initVars s = []) :
    (Stmt.liftInitsInLoopBodyM s σ).1.1 = [] := by
  match s with
  | .cmd c =>
      cases c with
      | init x ty rhs md => simp [Stmt.initVars] at h_iv
      | set x rhs md => simp [Stmt.liftInitsInLoopBodyM]
      | assert l e md => simp [Stmt.liftInitsInLoopBodyM]
      | assume l e md => simp [Stmt.liftInitsInLoopBodyM]
      | cover l e md => simp [Stmt.liftInitsInLoopBodyM]
  | .block lbl bss md =>
      have h_bss : Block.initVars bss = [] := by simpa [Stmt.initVars] using h_iv
      rw [Stmt.liftInitsInLoopBodyM_block_harvest,
          Block.liftInitsInLoopBodyM_fst_no_inits bss σ h_bss]
  | .ite g tss ess md =>
      have h_split : Block.initVars tss = [] ∧ Block.initVars ess = [] := by
        have htot : Block.initVars tss ++ Block.initVars ess = [] := by
          simpa [Stmt.initVars] using h_iv
        exact List.append_eq_nil_iff.mp htot
      rw [Stmt.liftInitsInLoopBodyM_ite_harvest,
          Block.liftInitsInLoopBodyM_fst_no_inits tss σ h_split.1,
          Block.liftInitsInLoopBodyM_fst_no_inits ess _ h_split.2,
          List.append_nil]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBodyM]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBodyM]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBodyM]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBodyM]
  termination_by sizeOf s

/-- Under `Block.initVars ss = []`, the harvested havoc prelude is empty. -/
private theorem Block.liftInitsInLoopBodyM_fst_no_inits
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_iv : Block.initVars ss = []) :
    (Block.liftInitsInLoopBodyM ss σ).1.1 = [] := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM]
  | s :: rest =>
      have h_split : Stmt.initVars s = [] ∧ Block.initVars rest = [] := by
        have htot : Stmt.initVars s ++ Block.initVars rest = [] := by
          simpa [Block.initVars] using h_iv
        exact List.append_eq_nil_iff.mp htot
      rw [Block.liftInitsInLoopBodyM_cons_harvest,
          Stmt.liftInitsInLoopBodyM_fst_no_inits s σ h_split.1,
          Block.liftInitsInLoopBodyM_fst_no_inits rest _ h_split.2,
          List.append_nil]
  termination_by sizeOf ss
end

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
/-- Under `Stmt.initVars s = []`, the residual is `s` unchanged. -/
private theorem Stmt.liftInitsInLoopBodyM_snd_no_inits
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h_iv : Stmt.initVars s = []) :
    (Stmt.liftInitsInLoopBodyM s σ).1.2.2 = [s] := by
  match s with
  | .cmd c =>
      cases c with
      | init x ty rhs md => simp [Stmt.initVars] at h_iv
      | set x rhs md => simp [Stmt.liftInitsInLoopBodyM]
      | assert l e md => simp [Stmt.liftInitsInLoopBodyM]
      | assume l e md => simp [Stmt.liftInitsInLoopBodyM]
      | cover l e md => simp [Stmt.liftInitsInLoopBodyM]
  | .block lbl bss md =>
      have h_bss : Block.initVars bss = [] := by simpa [Stmt.initVars] using h_iv
      rw [Stmt.liftInitsInLoopBodyM_block_residual,
          Block.liftInitsInLoopBodyM_snd_no_inits bss σ h_bss]
  | .ite g tss ess md =>
      have h_split : Block.initVars tss = [] ∧ Block.initVars ess = [] := by
        have htot : Block.initVars tss ++ Block.initVars ess = [] := by
          simpa [Stmt.initVars] using h_iv
        exact List.append_eq_nil_iff.mp htot
      rw [Stmt.liftInitsInLoopBodyM_ite_residual,
          Block.liftInitsInLoopBodyM_snd_no_inits tss σ h_split.1,
          Block.liftInitsInLoopBodyM_snd_no_inits ess _ h_split.2]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBodyM]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBodyM]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBodyM]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBodyM]
  termination_by sizeOf s

/-- Under `Block.initVars ss = []`, the residual is `ss` unchanged. -/
private theorem Block.liftInitsInLoopBodyM_snd_no_inits
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_iv : Block.initVars ss = []) :
    (Block.liftInitsInLoopBodyM ss σ).1.2.2 = ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM]
  | s :: rest =>
      have h_split : Stmt.initVars s = [] ∧ Block.initVars rest = [] := by
        have htot : Stmt.initVars s ++ Block.initVars rest = [] := by
          simpa [Block.initVars] using h_iv
        exact List.append_eq_nil_iff.mp htot
      rw [Block.liftInitsInLoopBodyM_cons_residual,
          Stmt.liftInitsInLoopBodyM_snd_no_inits s σ h_split.1,
          Block.liftInitsInLoopBodyM_snd_no_inits rest _ h_split.2,
          List.singleton_append]
  termination_by sizeOf ss
end

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
/-- Pure-wrapper identity of `Stmt.liftInitsInLoopBody` when `initVars = []`. -/
theorem Stmt.liftInitsInLoopBody_no_inits_eq
    (s : Stmt P (Cmd P)) (h_iv : Stmt.initVars s = []) :
    Stmt.liftInitsInLoopBody s = ([], [s]) := by
  rw [Stmt.liftInitsInLoopBody]
  rw [Stmt.liftInitsInLoopBodyM_fst_no_inits s StringGenState.emp h_iv,
      Stmt.liftInitsInLoopBodyM_snd_no_inits s StringGenState.emp h_iv]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
/-- Pure-wrapper identity of `Block.liftInitsInLoopBody` when `initVars = []`. -/
theorem Block.liftInitsInLoopBody_no_inits_eq
    (ss : List (Stmt P (Cmd P))) (h_iv : Block.initVars ss = []) :
    Block.liftInitsInLoopBody ss = ([], ss) := by
  rw [Block.liftInitsInLoopBody]
  rw [Block.liftInitsInLoopBodyM_fst_no_inits ss StringGenState.emp h_iv,
      Block.liftInitsInLoopBodyM_snd_no_inits ss StringGenState.emp h_iv]

/-! ### Per-constructor residual (`.snd`) reduction of the pure wrapper

`liftInitsInLoopBody` is now a projection of the monadic pass, so the old
`simp only [Stmt.liftInitsInLoopBody]` unfold no longer reduces `.snd` to the
constructor shape. These name-agnostic equations re-expose the per-constructor
residual shape on the wrapper, so the shape-only `_snd_*` postcondition proofs
(`namesFreshInExprs`, `hoistedNamesFreshInGuards`, `initVars_subset`, …) in
`LoopInitHoistRewrite.lean` / `LoopInitHoistFreshness.lean` can drive the
structural recursion exactly as before — just `rw`/`simp` with these instead
of the old definitional unfold. The init→set conversion is name-preserving
(original `x` retained in the residual), which is why these are independent of
the fresh names harvested into `.fst`. -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_cmd_init
    (x : P.Ident) (ty : P.Ty) (rhs : ExprOrNondet P) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.cmd (.init x ty rhs md))).snd =
      [.cmd (.set x rhs md)] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_cmd_set
    (x : P.Ident) (rhs : ExprOrNondet P) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.cmd (.set x rhs md))).snd =
      [.cmd (.set x rhs md)] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_cmd_assert
    (l : String) (e : P.Expr) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.cmd (.assert l e md))).snd =
      [.cmd (.assert l e md)] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_cmd_assume
    (l : String) (e : P.Expr) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.cmd (.assume l e md))).snd =
      [.cmd (.assume l e md)] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_cmd_cover
    (l : String) (e : P.Expr) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.cmd (.cover l e md))).snd =
      [.cmd (.cover l e md)] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_block
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.block lbl bss md)).snd =
      [.block lbl (Block.liftInitsInLoopBody bss).snd md] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp,
      Stmt.liftInitsInLoopBodyM_block_residual,
      ← Block.liftInitsInLoopBody_snd_eq bss StringGenState.emp]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_ite
    (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.ite g tss ess md)).snd =
      [.ite g (Block.liftInitsInLoopBody tss).snd
              (Block.liftInitsInLoopBody ess).snd md] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp,
      Stmt.liftInitsInLoopBodyM_ite_residual]
  rw [← Block.liftInitsInLoopBody_snd_eq tss StringGenState.emp,
      ← Block.liftInitsInLoopBody_snd_eq ess
        (Block.liftInitsInLoopBodyM tss StringGenState.emp).2]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_loop
    (g : ExprOrNondet P) (m : Option P.Expr)
    (inv : List (String × P.Expr)) (body : List (Stmt P (Cmd P)))
    (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.loop g m inv body md)).snd =
      [.loop g m inv body md] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_exit
    (lbl : String) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.exit lbl md)).snd = [.exit lbl md] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_funcDecl
    (d : PureFunc P) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.funcDecl d md)).snd = [.funcDecl d md] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Stmt.liftInitsInLoopBody_snd_typeDecl
    (t : TypeConstructor) (md : MetaData P) :
    (Stmt.liftInitsInLoopBody (.typeDecl t md)).snd = [.typeDecl t md] := by
  rw [Stmt.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Stmt.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Block.liftInitsInLoopBody_snd_nil :
    (Block.liftInitsInLoopBody ([] : List (Stmt P (Cmd P)))).snd = [] := by
  rw [Block.liftInitsInLoopBody_snd_eq _ StringGenState.emp]
  simp [Block.liftInitsInLoopBodyM]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
@[simp] theorem Block.liftInitsInLoopBody_snd_cons
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) :
    (Block.liftInitsInLoopBody (s :: rest)).snd =
      (Stmt.liftInitsInLoopBody s).snd ++ (Block.liftInitsInLoopBody rest).snd := by
  rw [Block.liftInitsInLoopBody_snd_eq _ StringGenState.emp,
      Block.liftInitsInLoopBodyM_cons_residual,
      ← Stmt.liftInitsInLoopBody_snd_eq s StringGenState.emp,
      ← Block.liftInitsInLoopBody_snd_eq rest
        (Stmt.liftInitsInLoopBodyM s StringGenState.emp).2]

/-! ### `allLoopBodiesInitFree` is preserved by the lift residual -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
/-- The residual of `Stmt.liftInitsInLoopBodyM s` has the same
`allLoopBodiesInitFree` as `s` (the lift never touches loop bodies, and turns
inits into sets which carry no loop). -/
private theorem Stmt.liftInitsInLoopBodyM_snd_allLoopBodiesInitFree
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.allLoopBodiesInitFree (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      Stmt.allLoopBodiesInitFree s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.allLoopBodiesInitFree,
              Stmt.allLoopBodiesInitFree]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      simp only [Block.allLoopBodiesInitFree, Stmt.allLoopBodiesInitFree, Bool.and_true]
      exact Block.liftInitsInLoopBodyM_snd_allLoopBodiesInitFree bss σ
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      simp only [Block.allLoopBodiesInitFree, Stmt.allLoopBodiesInitFree, Bool.and_true]
      rw [Block.liftInitsInLoopBodyM_snd_allLoopBodiesInitFree tss σ,
          Block.liftInitsInLoopBodyM_snd_allLoopBodiesInitFree ess _]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.allLoopBodiesInitFree,
            Stmt.allLoopBodiesInitFree]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.allLoopBodiesInitFree,
            Stmt.allLoopBodiesInitFree]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.allLoopBodiesInitFree,
            Stmt.allLoopBodiesInitFree]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.allLoopBodiesInitFree,
            Stmt.allLoopBodiesInitFree]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBodyM_snd_allLoopBodiesInitFree
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.allLoopBodiesInitFree (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      Block.allLoopBodiesInitFree ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.allLoopBodiesInitFree]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual,
          Block.allLoopBodiesInitFree_append]
      simp only [Block.allLoopBodiesInitFree]
      rw [Stmt.liftInitsInLoopBodyM_snd_allLoopBodiesInitFree s σ,
          Block.liftInitsInLoopBodyM_snd_allLoopBodiesInitFree rest _]
  termination_by sizeOf ss
end

/-! ### `noInitsAnywhere` of the lift residual (under the input precondition) -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
/-- Under `Stmt.allLoopBodiesInitFree s`, the residual of
`Stmt.liftInitsInLoopBodyM s` has no inits anywhere: every init was lifted to
a fresh prelude havoc (harvested in `.1.1`), and the precondition guarantees
nested loops were already init-free. -/
private theorem Stmt.liftInitsInLoopBodyM_snd_noInitsAnywhere
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.allLoopBodiesInitFree s = true) :
    Block.noInitsAnywhere (Stmt.liftInitsInLoopBodyM s σ).1.2.2 = true := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.noInitsAnywhere,
              Stmt.noInitsAnywhere]
  | .block lbl bss md =>
      have h_bss : Block.allLoopBodiesInitFree bss = true := by
        rw [Stmt.allLoopBodiesInitFree] at h; exact h
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      simp only [Block.noInitsAnywhere, Stmt.noInitsAnywhere, Bool.and_true]
      exact Block.liftInitsInLoopBodyM_snd_noInitsAnywhere bss σ h_bss
  | .ite g tss ess md =>
      have h_branches : Block.allLoopBodiesInitFree tss = true ∧
                        Block.allLoopBodiesInitFree ess = true := by
        rw [Stmt.allLoopBodiesInitFree, Bool.and_eq_true] at h; exact h
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      simp only [Block.noInitsAnywhere, Stmt.noInitsAnywhere, Bool.and_true,
                 Block.liftInitsInLoopBodyM_snd_noInitsAnywhere tss σ h_branches.1,
                 Block.liftInitsInLoopBodyM_snd_noInitsAnywhere ess _ h_branches.2]
  | .loop g m inv body md =>
      have h_body_nia : Block.noInitsAnywhere body = true := by
        rw [Stmt.allLoopBodiesInitFree, Bool.and_eq_true] at h; exact h.1
      simp [Stmt.liftInitsInLoopBodyM, Block.noInitsAnywhere,
            Stmt.noInitsAnywhere, h_body_nia]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBodyM_snd_noInitsAnywhere
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.allLoopBodiesInitFree ss = true) :
    Block.noInitsAnywhere (Block.liftInitsInLoopBodyM ss σ).1.2.2 = true := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.noInitsAnywhere]
  | s :: rest =>
      rw [Block.allLoopBodiesInitFree, Bool.and_eq_true] at h
      rw [Block.liftInitsInLoopBodyM_cons_residual, Block.noInitsAnywhere_append]
      simp only [Stmt.liftInitsInLoopBodyM_snd_noInitsAnywhere s σ h.1,
                 Block.liftInitsInLoopBodyM_snd_noInitsAnywhere rest _ h.2,
                 Bool.and_true]
  termination_by sizeOf ss
end

/-! ### Output-projection (`.1`) equations for the top-level pass

Like the lift, the `hoistLoopPrefixInitsM` arms destructure recursive calls
with `let … := …` patterns. These per-constructor projections of the output
list `.1` let the postcondition proofs `rw` directly against the recursive
sub-outputs. The `.loop` arm is the interesting one: the output is the fresh
havoc prelude (mapped to `.cmd`) followed by the rewritten loop, where the
body has been renamed by `Block.applyRenames`. -/

private theorem Stmt.hoistLoopPrefixInitsM_block_out
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.hoistLoopPrefixInitsM (.block lbl bss md) σ).1 =
      [Stmt.block lbl (Block.hoistLoopPrefixInitsM bss σ).1 md] := by
  rw [Stmt.hoistLoopPrefixInitsM]
  rcases h : Block.hoistLoopPrefixInitsM bss σ with ⟨bss', σ'⟩
  simp only [h]

private theorem Stmt.hoistLoopPrefixInitsM_ite_out
    (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.hoistLoopPrefixInitsM (.ite g tss ess md) σ).1 =
      [Stmt.ite g (Block.hoistLoopPrefixInitsM tss σ).1
                  (Block.hoistLoopPrefixInitsM ess
                    (Block.hoistLoopPrefixInitsM tss σ).2).1 md] := by
  rw [Stmt.hoistLoopPrefixInitsM]
  rcases h₁ : Block.hoistLoopPrefixInitsM tss σ with ⟨tss', σ₁⟩
  rcases h₂ : Block.hoistLoopPrefixInitsM ess σ₁ with ⟨ess', σ₂⟩
  simp only [h₁, h₂]

/-- The `.loop` arm output: the fresh havoc prelude followed by the loop whose
body is the lift residual after `applyRenames`. Here `body₁` is the
post-order-processed body, `σ₁` the state after, and `lifted` the lift of
`body₁` from `σ₁`. -/
private theorem Stmt.hoistLoopPrefixInitsM_loop_out
    (g : ExprOrNondet P) (m : Option P.Expr)
    (inv : List (String × P.Expr)) (body : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.hoistLoopPrefixInitsM (.loop g m inv body md) σ).1 =
      (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
        (Block.hoistLoopPrefixInitsM body σ).2).1.1.map Stmt.cmd ++
      [Stmt.loop g m inv
        (Block.applyRenames
          (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
            (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
          (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
            (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) md] := by
  rw [Stmt.hoistLoopPrefixInitsM]
  rcases h₁ : Block.hoistLoopPrefixInitsM body σ with ⟨body₁, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM body₁ σ₁ with ⟨⟨havocs, renames, body₂⟩, σ₂⟩
  simp only [h₁, h₂]

private theorem Block.hoistLoopPrefixInitsM_cons_out
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.hoistLoopPrefixInitsM (s :: rest) σ).1 =
      (Stmt.hoistLoopPrefixInitsM s σ).1 ++
        (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).1 := by
  rw [Block.hoistLoopPrefixInitsM]
  rcases h₁ : Stmt.hoistLoopPrefixInitsM s σ with ⟨ss_s, σ₁⟩
  rcases h₂ : Block.hoistLoopPrefixInitsM rest σ₁ with ⟨ss_r, σ₂⟩
  simp only [h₁, h₂]

/-! ### Generator-state monotonicity of the pass (`GenStep`)

The pass threads a single monotone `StringGenState`; the only place it draws a
fresh name is `liftInitsInLoopBodyM`'s `.init` arm, which calls
`StringGenState.gen`. Hence the final state of every monadic walker is a
`StringGenState.GenStep` from its input: well-formedness is preserved and the
set of produced labels only grows (never shrinks). The proof mirrors the pass
recursion exactly, composing per-substructure steps via `GenStep.trans` and
discharging the `.init` leaf via `GenStep.of_gen`. This is the monotonicity
backbone that lets the §E mutual re-establish its generator-state
preconditions at the advanced state in the `cons`/`.ite`/`.loop` arms. -/

open StringGenState (GenStep) in
omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
/-- The lift's final generator state is a `GenStep` from its input. -/
theorem Stmt.liftInitsInLoopBodyM_genStep
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    GenStep σ (Stmt.liftInitsInLoopBodyM s σ).2 := by
  match s with
  | .cmd c =>
      cases c with
      | init x ty rhs md =>
          rw [Stmt.liftInitsInLoopBodyM]
          exact StringGenState.GenStep.of_gen hoistFreshPrefix σ
      | set x rhs md => simp only [Stmt.liftInitsInLoopBodyM]; exact GenStep.refl σ
      | assert l e md => simp only [Stmt.liftInitsInLoopBodyM]; exact GenStep.refl σ
      | assume l e md => simp only [Stmt.liftInitsInLoopBodyM]; exact GenStep.refl σ
      | cover l e md => simp only [Stmt.liftInitsInLoopBodyM]; exact GenStep.refl σ
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM]
      rcases h : Block.liftInitsInLoopBodyM bss σ with ⟨⟨hs, rn, bss'⟩, σ'⟩
      simp only [h]
      have := Block.liftInitsInLoopBodyM_genStep bss σ
      rw [h] at this; exact this
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM]
      rcases h₁ : Block.liftInitsInLoopBodyM tss σ with ⟨⟨ths, trn, tss'⟩, σ₁⟩
      rcases h₂ : Block.liftInitsInLoopBodyM ess σ₁ with ⟨⟨ehs, ern, ess'⟩, σ₂⟩
      simp only [h₁, h₂]
      have hstep1 := Block.liftInitsInLoopBodyM_genStep tss σ
      rw [h₁] at hstep1
      have hstep2 := Block.liftInitsInLoopBodyM_genStep ess σ₁
      rw [h₂] at hstep2
      exact hstep1.trans hstep2
  | .loop g m inv body md => rw [Stmt.liftInitsInLoopBodyM]; exact GenStep.refl σ
  | .exit lbl md => rw [Stmt.liftInitsInLoopBodyM]; exact GenStep.refl σ
  | .funcDecl d md => rw [Stmt.liftInitsInLoopBodyM]; exact GenStep.refl σ
  | .typeDecl t md => rw [Stmt.liftInitsInLoopBodyM]; exact GenStep.refl σ
  termination_by sizeOf s

/-- The block-level lift's final generator state is a `GenStep` from its input. -/
theorem Block.liftInitsInLoopBodyM_genStep
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    GenStep σ (Block.liftInitsInLoopBodyM ss σ).2 := by
  match ss with
  | [] => rw [Block.liftInitsInLoopBodyM]; exact GenStep.refl σ
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM]
      rcases h₁ : Stmt.liftInitsInLoopBodyM s σ with ⟨⟨hs_s, rn_s, ss_s⟩, σ₁⟩
      rcases h₂ : Block.liftInitsInLoopBodyM rest σ₁ with ⟨⟨hs_r, rn_r, ss_r⟩, σ₂⟩
      simp only [h₁, h₂]
      have hstep1 := Stmt.liftInitsInLoopBodyM_genStep s σ
      rw [h₁] at hstep1
      have hstep2 := Block.liftInitsInLoopBodyM_genStep rest σ₁
      rw [h₂] at hstep2
      exact hstep1.trans hstep2
  termination_by sizeOf ss
end

/-! ### The lift's freshly-minted labels carry the hoist mint kind `Q`.

Every label the lift adds to the generator state is minted by `gen
hoistFreshPrefix` (the lift's only generator call, at each `.init`), so it lies
in the image of the mint witness `hQmint`.  This is the building block that lets
the source-kind-freedom hypothesis (`∀ str, Q str → …`) discharge the
generator-step threading of the σ-membership freshness invariant: a label the
lift adds over `σ` is `Q`-kind, hence the kind-free source names avoid it. -/

open StringGenState (GenStep) in
omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
/-- Every label the statement lift adds over `σ` carries the mint kind `Q`. -/
theorem Stmt.liftInitsInLoopBodyM_genStep_delta_Q {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ str ∈ StringGenState.stringGens (Stmt.liftInitsInLoopBodyM s σ).2,
      str ∉ StringGenState.stringGens σ → Q str := by
  match s with
  | .cmd c =>
      cases c with
      | init x ty rhs md =>
          intro str h_in h_nin
          rw [Stmt.liftInitsInLoopBodyM] at h_in
          rw [StringGenState.stringGens_gen, List.mem_cons] at h_in
          rcases h_in with h_new | h_old
          · subst h_new; exact hQmint σ
          · exact absurd h_old h_nin
      | set x rhs md =>
          intro str h_in h_nin
          simp only [Stmt.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
      | assert l e md =>
          intro str h_in h_nin
          simp only [Stmt.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
      | assume l e md =>
          intro str h_in h_nin
          simp only [Stmt.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
      | cover l e md =>
          intro str h_in h_nin
          simp only [Stmt.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
  | .block lbl bss md =>
      intro str h_in h_nin
      have h_state : (Stmt.liftInitsInLoopBodyM (.block lbl bss md) σ).2
          = (Block.liftInitsInLoopBodyM bss σ).2 := by
        rw [Stmt.liftInitsInLoopBodyM]
        rcases h : Block.liftInitsInLoopBodyM bss σ with ⟨⟨hs, rn, bss'⟩, σ'⟩
        simp only [h]
      rw [h_state] at h_in
      exact Block.liftInitsInLoopBodyM_genStep_delta_Q hQmint bss σ str h_in h_nin
  | .ite g tss ess md =>
      intro str h_in h_nin
      have h_state : (Stmt.liftInitsInLoopBodyM (.ite g tss ess md) σ).2
          = (Block.liftInitsInLoopBodyM ess (Block.liftInitsInLoopBodyM tss σ).2).2 := by
        rw [Stmt.liftInitsInLoopBodyM]
        rcases h₁ : Block.liftInitsInLoopBodyM tss σ with ⟨⟨ths, trn, tss'⟩, σ₁⟩
        rcases h₂ : Block.liftInitsInLoopBodyM ess σ₁ with ⟨⟨ehs, ern, ess'⟩, σ₂⟩
        simp only [h₁, h₂]
      rw [h_state] at h_in
      by_cases h_mid : str ∈ StringGenState.stringGens (Block.liftInitsInLoopBodyM tss σ).2
      · exact Block.liftInitsInLoopBodyM_genStep_delta_Q hQmint tss σ str h_mid h_nin
      · exact Block.liftInitsInLoopBodyM_genStep_delta_Q hQmint ess
          (Block.liftInitsInLoopBodyM tss σ).2 str h_in h_mid
  | .loop g m inv body md =>
      intro str h_in h_nin
      simp only [Stmt.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
  | .exit lbl md =>
      intro str h_in h_nin
      simp only [Stmt.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
  | .funcDecl d md =>
      intro str h_in h_nin
      simp only [Stmt.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
  | .typeDecl t md =>
      intro str h_in h_nin
      simp only [Stmt.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
  termination_by sizeOf s

/-- Every label the block lift adds over `σ` carries the mint kind `Q`. -/
theorem Block.liftInitsInLoopBodyM_genStep_delta_Q {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ str ∈ StringGenState.stringGens (Block.liftInitsInLoopBodyM ss σ).2,
      str ∉ StringGenState.stringGens σ → Q str := by
  match ss with
  | [] =>
      intro str h_in h_nin
      rw [Block.liftInitsInLoopBodyM] at h_in; exact absurd h_in h_nin
  | s :: rest =>
      intro str h_in h_nin
      have h_state : (Block.liftInitsInLoopBodyM (s :: rest) σ).2
          = (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).2 := by
        rw [Block.liftInitsInLoopBodyM]
        rcases h₁ : Stmt.liftInitsInLoopBodyM s σ with ⟨⟨hs_s, rn_s, ss_s⟩, σ₁⟩
        rcases h₂ : Block.liftInitsInLoopBodyM rest σ₁ with ⟨⟨hs_r, rn_r, ss_r⟩, σ₂⟩
        simp only [h₁, h₂]
      rw [h_state] at h_in
      by_cases h_mid : str ∈ StringGenState.stringGens (Stmt.liftInitsInLoopBodyM s σ).2
      · exact Stmt.liftInitsInLoopBodyM_genStep_delta_Q hQmint s σ str h_mid h_nin
      · exact Block.liftInitsInLoopBodyM_genStep_delta_Q hQmint rest
          (Stmt.liftInitsInLoopBodyM s σ).2 str h_in h_mid
  termination_by sizeOf ss
end

open StringGenState (GenStep) in
mutual
/-- The pass's final generator state is a `GenStep` from its input. -/
theorem Stmt.hoistLoopPrefixInitsM_genStep
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    GenStep σ (Stmt.hoistLoopPrefixInitsM s σ).2 := by
  match s with
  | .cmd c => rw [Stmt.hoistLoopPrefixInitsM]; exact GenStep.refl σ
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM]
      rcases h : Block.hoistLoopPrefixInitsM bss σ with ⟨bss', σ'⟩
      simp only [h]
      have := Block.hoistLoopPrefixInitsM_genStep bss σ
      rw [h] at this; exact this
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM]
      rcases h₁ : Block.hoistLoopPrefixInitsM tss σ with ⟨tss', σ₁⟩
      rcases h₂ : Block.hoistLoopPrefixInitsM ess σ₁ with ⟨ess', σ₂⟩
      simp only [h₁, h₂]
      have hstep1 := Block.hoistLoopPrefixInitsM_genStep tss σ
      rw [h₁] at hstep1
      have hstep2 := Block.hoistLoopPrefixInitsM_genStep ess σ₁
      rw [h₂] at hstep2
      exact hstep1.trans hstep2
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM]
      rcases h₁ : Block.hoistLoopPrefixInitsM body σ with ⟨body₁, σ₁⟩
      rcases h₂ : Block.liftInitsInLoopBodyM body₁ σ₁ with ⟨⟨havocs, renames, body₂⟩, σ₂⟩
      simp only [h₁, h₂]
      have hstep1 := Block.hoistLoopPrefixInitsM_genStep body σ
      rw [h₁] at hstep1
      have hstep2 := Block.liftInitsInLoopBodyM_genStep body₁ σ₁
      rw [h₂] at hstep2
      exact hstep1.trans hstep2
  | .exit lbl md => rw [Stmt.hoistLoopPrefixInitsM]; exact GenStep.refl σ
  | .funcDecl d md => rw [Stmt.hoistLoopPrefixInitsM]; exact GenStep.refl σ
  | .typeDecl t md => rw [Stmt.hoistLoopPrefixInitsM]; exact GenStep.refl σ
  termination_by sizeOf s

/-- The block-level pass's final generator state is a `GenStep` from its
input. -/
theorem Block.hoistLoopPrefixInitsM_genStep
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    GenStep σ (Block.hoistLoopPrefixInitsM ss σ).2 := by
  match ss with
  | [] => rw [Block.hoistLoopPrefixInitsM]; exact GenStep.refl σ
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM]
      rcases h₁ : Stmt.hoistLoopPrefixInitsM s σ with ⟨ss_s, σ₁⟩
      rcases h₂ : Block.hoistLoopPrefixInitsM rest σ₁ with ⟨ss_r, σ₂⟩
      simp only [h₁, h₂]
      have hstep1 := Stmt.hoistLoopPrefixInitsM_genStep s σ
      rw [h₁] at hstep1
      have hstep2 := Block.hoistLoopPrefixInitsM_genStep rest σ₁
      rw [h₂] at hstep2
      exact hstep1.trans hstep2
  termination_by sizeOf ss
end

/-! ### The post-order pass's freshly-minted labels carry the mint kind `Q`.

Every label `hoistLoopPrefixInitsM` adds to the generator state is minted by
`gen hoistFreshPrefix` — either by the post-order recursion or by the nested
`liftInitsInLoopBodyM` of a `.loop` body — so it lies in the image of the mint
witness `hQmint`.  This is the pass-level companion of
`liftInitsInLoopBodyM_genStep_delta_Q`, and it is what lets the source
kind-freedom hypothesis discharge the generator-step threading of the
σ-membership freshness invariant in the §E `.cons`/`.ite` arms. -/

open StringGenState (GenStep) in
mutual
/-- Every label the statement pass adds over `σ` carries the mint kind `Q`. -/
theorem Stmt.hoistLoopPrefixInitsM_genStep_delta_Q {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ str ∈ StringGenState.stringGens (Stmt.hoistLoopPrefixInitsM s σ).2,
      str ∉ StringGenState.stringGens σ → Q str := by
  match s with
  | .cmd c =>
      intro str h_in h_nin
      rw [Stmt.hoistLoopPrefixInitsM] at h_in; exact absurd h_in h_nin
  | .block lbl bss md =>
      intro str h_in h_nin
      have h_state : (Stmt.hoistLoopPrefixInitsM (.block lbl bss md) σ).2
          = (Block.hoistLoopPrefixInitsM bss σ).2 := by
        rw [Stmt.hoistLoopPrefixInitsM]
        rcases h : Block.hoistLoopPrefixInitsM bss σ with ⟨bss', σ'⟩
        simp only [h]
      rw [h_state] at h_in
      exact Block.hoistLoopPrefixInitsM_genStep_delta_Q hQmint bss σ str h_in h_nin
  | .ite g tss ess md =>
      intro str h_in h_nin
      have h_state : (Stmt.hoistLoopPrefixInitsM (.ite g tss ess md) σ).2
          = (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).2 := by
        rw [Stmt.hoistLoopPrefixInitsM]
        rcases h₁ : Block.hoistLoopPrefixInitsM tss σ with ⟨tss', σ₁⟩
        rcases h₂ : Block.hoistLoopPrefixInitsM ess σ₁ with ⟨ess', σ₂⟩
        simp only [h₁, h₂]
      rw [h_state] at h_in
      by_cases h_mid : str ∈ StringGenState.stringGens (Block.hoistLoopPrefixInitsM tss σ).2
      · exact Block.hoistLoopPrefixInitsM_genStep_delta_Q hQmint tss σ str h_mid h_nin
      · exact Block.hoistLoopPrefixInitsM_genStep_delta_Q hQmint ess
          (Block.hoistLoopPrefixInitsM tss σ).2 str h_in h_mid
  | .loop g m inv body md =>
      intro str h_in h_nin
      -- output state = lift (post-order body₁) σ₁, where σ₁ = post-order body state.
      have h_state : (Stmt.hoistLoopPrefixInitsM (.loop g m inv body md) σ).2
          = (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).2 := by
        rw [Stmt.hoistLoopPrefixInitsM]
        rcases h₁ : Block.hoistLoopPrefixInitsM body σ with ⟨body₁, σ₁⟩
        rcases h₂ : Block.liftInitsInLoopBodyM body₁ σ₁ with ⟨⟨havocs, renames, body₂⟩, σ₂⟩
        simp only [h₁, h₂]
      rw [h_state] at h_in
      by_cases h_mid : str ∈ StringGenState.stringGens (Block.hoistLoopPrefixInitsM body σ).2
      · exact Block.hoistLoopPrefixInitsM_genStep_delta_Q hQmint body σ str h_mid h_nin
      · exact Block.liftInitsInLoopBodyM_genStep_delta_Q hQmint
          (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2
          str h_in h_mid
  | .exit lbl md =>
      intro str h_in h_nin
      rw [Stmt.hoistLoopPrefixInitsM] at h_in; exact absurd h_in h_nin
  | .funcDecl d md =>
      intro str h_in h_nin
      rw [Stmt.hoistLoopPrefixInitsM] at h_in; exact absurd h_in h_nin
  | .typeDecl t md =>
      intro str h_in h_nin
      rw [Stmt.hoistLoopPrefixInitsM] at h_in; exact absurd h_in h_nin
  termination_by sizeOf s

/-- Every label the block pass adds over `σ` carries the mint kind `Q`. -/
theorem Block.hoistLoopPrefixInitsM_genStep_delta_Q {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ str ∈ StringGenState.stringGens (Block.hoistLoopPrefixInitsM ss σ).2,
      str ∉ StringGenState.stringGens σ → Q str := by
  match ss with
  | [] =>
      intro str h_in h_nin
      rw [Block.hoistLoopPrefixInitsM] at h_in; exact absurd h_in h_nin
  | s :: rest =>
      intro str h_in h_nin
      have h_state : (Block.hoistLoopPrefixInitsM (s :: rest) σ).2
          = (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).2 := by
        rw [Block.hoistLoopPrefixInitsM]
        rcases h₁ : Stmt.hoistLoopPrefixInitsM s σ with ⟨ss_s, σ₁⟩
        rcases h₂ : Block.hoistLoopPrefixInitsM rest σ₁ with ⟨ss_r, σ₂⟩
        simp only [h₁, h₂]
      rw [h_state] at h_in
      by_cases h_mid : str ∈ StringGenState.stringGens (Stmt.hoistLoopPrefixInitsM s σ).2
      · exact Stmt.hoistLoopPrefixInitsM_genStep_delta_Q hQmint s σ str h_mid h_nin
      · exact Block.hoistLoopPrefixInitsM_genStep_delta_Q hQmint rest
          (Stmt.hoistLoopPrefixInitsM s σ).2 str h_in h_mid
  termination_by sizeOf ss
end

/-! ### Fresh-from-generator-state disjointness, and its threading

Every label a `GenStep` adds is suffix-shaped (`_<digits>`, the shape every
`StringGenState.gen` output carries). A source/user identifier that — viewed as
a string — lacks that suffix shape can therefore never coincide with a label
the generator added. This is the building block that discharges the §E
mutual's "the new fresh names are disjoint from the source names" obligation
from generator monotonicity alone. -/

/-- The §E fresh-from-σ precondition shape: every label already produced by
`σ`, injected into `P.Ident`, is disjoint from the source frame names `A`,
extra names `B`, and `.init` LHS names `ivs`. -/
def SrcNamesFreshFromGen (A B ivs : List P.Ident) (σ : StringGenState) : Prop :=
  ∀ str ∈ StringGenState.stringGens σ,
    HasIdent.ident (P := P) str ∉ A ∧
    HasIdent.ident (P := P) str ∉ B ∧
    HasIdent.ident (P := P) str ∉ ivs

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
/-- Kind-aware threading of the fresh-from-σ precondition across a `GenStep`.
The caller supplies `h_delta` recording that every newly-added label carries a
client kind `Q` (for the hoist pass, via `…_genStep_delta_Q` + the mint witness
`hQmint`).  It then needs only the `Q`-restricted source kind-freedom
`h_src_shapefree`, so a composition partner is never forced to keep *every*
generator-shaped name fresh — only labels of its own kind. -/
theorem SrcNamesFreshFromGen.genStep_of_delta {Q : String → Prop}
    {A B ivs : List P.Ident} {σ σ' : StringGenState}
    (h_delta : ∀ str ∈ StringGenState.stringGens σ',
      str ∉ StringGenState.stringGens σ → Q str)
    (h_src_shapefree :
      ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ A ∧
        HasIdent.ident (P := P) str ∉ B ∧
        HasIdent.ident (P := P) str ∉ ivs)
    (h_fresh : SrcNamesFreshFromGen (P := P) A B ivs σ) :
    SrcNamesFreshFromGen (P := P) A B ivs σ' := by
  intro str h_mem
  by_cases h_in_σ : str ∈ StringGenState.stringGens σ
  · exact h_fresh str h_in_σ
  · exact h_src_shapefree str (h_delta str h_mem h_in_σ)

/-! ### Top-level `allLoopBodiesInitFree` postcondition (monadic + pure) -/

mutual
/-- The output of `Stmt.hoistLoopPrefixInitsM s σ` satisfies
`allLoopBodiesInitFree`. -/
private theorem Stmt.hoistLoopPrefixInitsM_allLoopBodiesInitFree
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.allLoopBodiesInitFree (Stmt.hoistLoopPrefixInitsM s σ).1 = true := by
  match s with
  | .cmd c =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.allLoopBodiesInitFree,
            Stmt.allLoopBodiesInitFree]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.allLoopBodiesInitFree, Stmt.allLoopBodiesInitFree, Bool.and_true]
      exact Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree bss σ
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      simp only [Block.allLoopBodiesInitFree, Stmt.allLoopBodiesInitFree, Bool.and_true,
                 Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree tss σ,
                 Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree ess _]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      -- the post-order-processed body and the state after it
      have h_body₁_albif :
          Block.allLoopBodiesInitFree (Block.hoistLoopPrefixInitsM body σ).1 = true :=
        Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree body σ
      have h_body₂_albif :
          Block.allLoopBodiesInitFree
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 = true := by
        rw [Block.liftInitsInLoopBodyM_snd_allLoopBodiesInitFree]; exact h_body₁_albif
      have h_body₂_nia :
          Block.noInitsAnywhere
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 = true :=
        Block.liftInitsInLoopBodyM_snd_noInitsAnywhere _ _ h_body₁_albif
      rw [Block.allLoopBodiesInitFree_append]
      simp only [Block.allLoopBodiesInitFree_map_cmd, Block.allLoopBodiesInitFree,
                 Stmt.allLoopBodiesInitFree, Bool.true_and, Bool.and_true]
      rw [Block.applyRenames_noInitsAnywhere, Block.applyRenames_allLoopBodiesInitFree]
      exact Bool.and_eq_true _ _ |>.mpr ⟨h_body₂_nia, h_body₂_albif⟩
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.allLoopBodiesInitFree,
            Stmt.allLoopBodiesInitFree]
  | .funcDecl d md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.allLoopBodiesInitFree,
            Stmt.allLoopBodiesInitFree]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.allLoopBodiesInitFree,
            Stmt.allLoopBodiesInitFree]
  termination_by sizeOf s

private theorem Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.allLoopBodiesInitFree (Block.hoistLoopPrefixInitsM ss σ).1 = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInitsM, Block.allLoopBodiesInitFree]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.allLoopBodiesInitFree_append]
      simp only [Stmt.hoistLoopPrefixInitsM_allLoopBodiesInitFree s σ,
                 Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree rest _, Bool.and_true]
  termination_by sizeOf ss
end

/-- Top-level Phase 8 §E5 (Option A) structural postcondition (monadic
fresh-name pass): `Block.hoistLoopPrefixInits` produces a block where every
`.loop` body contains no `.init` commands at any nesting depth. -/
theorem Block.hoistLoopPrefixInits_allLoopBodiesInitFree
    (ss : List (Stmt P (Cmd P))) :
    Block.allLoopBodiesInitFree (Block.hoistLoopPrefixInits ss) = true :=
  Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree ss StringGenState.emp

/-! ### Bridge: `allLoopBodiesInitFree` implies `loopBodyNoInits`

`allLoopBodiesInitFree` is strictly stronger: at the `.loop` arm it requires
`noInitsAnywhere body` (no inits in the body at any depth), which entails
`(Block.initVars body).isEmpty` (the predicate `loopBodyNoInits` requires).
This lets us derive the original `loopBodyNoInits` postcondition from the
already-proven `allLoopBodiesInitFree` one. The bridges do not depend on the
pass at all (pure facts about the structural predicates). -/

omit [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
/-- No inits anywhere ⇒ the deep `initVars` list is empty (`= []`). -/
private theorem Stmt.initVars_eq_nil_of_noInitsAnywhere
    (s : Stmt P (Cmd P)) (h : Stmt.noInitsAnywhere s = true) :
    Stmt.initVars s = [] := by
  match s with
  | .cmd c =>
      cases c <;> simp_all [Stmt.noInitsAnywhere, Stmt.initVars]
  | .block lbl bss md =>
      rw [Stmt.noInitsAnywhere] at h
      simp only [Stmt.initVars_block]
      exact Block.initVars_eq_nil_of_noInitsAnywhere bss h
  | .ite g tss ess md =>
      rw [Stmt.noInitsAnywhere, Bool.and_eq_true] at h
      simp only [Stmt.initVars_ite]
      rw [Block.initVars_eq_nil_of_noInitsAnywhere tss h.1,
          Block.initVars_eq_nil_of_noInitsAnywhere ess h.2, List.append_nil]
  | .loop g m inv bss md =>
      rw [Stmt.noInitsAnywhere] at h
      simp only [Stmt.initVars_loop]
      exact Block.initVars_eq_nil_of_noInitsAnywhere bss h
  | .exit lbl md => simp [Stmt.initVars]
  | .funcDecl d md => simp [Stmt.initVars]
  | .typeDecl t md => simp [Stmt.initVars]
  termination_by sizeOf s

private theorem Block.initVars_eq_nil_of_noInitsAnywhere
    (ss : List (Stmt P (Cmd P))) (h : Block.noInitsAnywhere ss = true) :
    Block.initVars ss = [] := by
  match ss with
  | [] => simp [Block.initVars]
  | s :: rest =>
      rw [Block.noInitsAnywhere, Bool.and_eq_true] at h
      simp only [Block.initVars_cons]
      rw [Stmt.initVars_eq_nil_of_noInitsAnywhere s h.1,
          Block.initVars_eq_nil_of_noInitsAnywhere rest h.2, List.append_nil]
  termination_by sizeOf ss
end

omit [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
private theorem Stmt.loopBodyNoInits_of_allLoopBodiesInitFree
    (s : Stmt P (Cmd P)) (h : Stmt.allLoopBodiesInitFree s = true) :
    Stmt.loopBodyNoInits s = true := by
  match s with
  | .cmd c => simp [Stmt.loopBodyNoInits]
  | .block lbl bss md =>
      rw [Stmt.allLoopBodiesInitFree] at h
      simp only [Stmt.loopBodyNoInits]
      exact Block.loopBodyNoInits_of_allLoopBodiesInitFree bss h
  | .ite g tss ess md =>
      rw [Stmt.allLoopBodiesInitFree, Bool.and_eq_true] at h
      simp only [Stmt.loopBodyNoInits,
                 Block.loopBodyNoInits_of_allLoopBodiesInitFree tss h.1,
                 Block.loopBodyNoInits_of_allLoopBodiesInitFree ess h.2, Bool.and_true]
  | .loop g m inv bss md =>
      rw [Stmt.allLoopBodiesInitFree, Bool.and_eq_true] at h
      simp only [Stmt.loopBodyNoInits,
                 Block.loopBodyNoInits_of_allLoopBodiesInitFree bss h.2,
                 Block.initVars_eq_nil_of_noInitsAnywhere bss h.1,
                 List.isEmpty_nil, Bool.and_true]
  | .exit lbl md => simp [Stmt.loopBodyNoInits]
  | .funcDecl d md => simp [Stmt.loopBodyNoInits]
  | .typeDecl t md => simp [Stmt.loopBodyNoInits]
  termination_by sizeOf s

private theorem Block.loopBodyNoInits_of_allLoopBodiesInitFree
    (ss : List (Stmt P (Cmd P))) (h : Block.allLoopBodiesInitFree ss = true) :
    Block.loopBodyNoInits ss = true := by
  match ss with
  | [] => simp [Block.loopBodyNoInits]
  | s :: rest =>
      rw [Block.allLoopBodiesInitFree, Bool.and_eq_true] at h
      simp only [Block.loopBodyNoInits,
                 Stmt.loopBodyNoInits_of_allLoopBodiesInitFree s h.1,
                 Block.loopBodyNoInits_of_allLoopBodiesInitFree rest h.2, Bool.and_true]
  termination_by sizeOf ss
end

/-- The original Phase 8 §E structural postcondition: the output of the
hoisting pass has `loopBodyNoInits = true` (every `.loop` body is init-free at
the top level). Derived from the stronger `allLoopBodiesInitFree`. -/
theorem hoistLoopPrefixInits_satisfies_loopBodyNoInits
    (ss : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (Block.hoistLoopPrefixInits ss) = true :=
  Block.loopBodyNoInits_of_allLoopBodiesInitFree _
    (Block.hoistLoopPrefixInits_allLoopBodiesInitFree ss)

/-! ### `loopMeasureNone` is preserved by the pass

The lift never changes any loop's `measure` slot (it does not recurse into
loops); `applyRenames` maps measures by `Option.map` so `m.isNone` is
unchanged (`Block.applyRenames_loopMeasureNone`); the fresh havoc prelude is
all `.cmd`s. Hence the whole pass preserves `loopMeasureNone`. -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
private theorem Stmt.liftInitsInLoopBodyM_snd_loopMeasureNone
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.loopMeasureNone (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      Stmt.loopMeasureNone s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      simp only [Block.loopMeasureNone, Stmt.loopMeasureNone, Bool.and_true]
      exact Block.liftInitsInLoopBodyM_snd_loopMeasureNone bss σ
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      simp only [Block.loopMeasureNone, Stmt.loopMeasureNone, Bool.and_true,
                 Block.liftInitsInLoopBodyM_snd_loopMeasureNone tss σ,
                 Block.liftInitsInLoopBodyM_snd_loopMeasureNone ess _]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBodyM_snd_loopMeasureNone
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.loopMeasureNone (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      Block.loopMeasureNone ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.loopMeasureNone]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual, Block.loopMeasureNone_append,
          Stmt.liftInitsInLoopBodyM_snd_loopMeasureNone s σ,
          Block.liftInitsInLoopBodyM_snd_loopMeasureNone rest _, Block.loopMeasureNone]
  termination_by sizeOf ss
end

mutual
private theorem Stmt.hoistLoopPrefixInitsM_loopMeasureNone
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.loopMeasureNone (Stmt.hoistLoopPrefixInitsM s σ).1 =
      Stmt.loopMeasureNone s := by
  match s with
  | .cmd c =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.loopMeasureNone, Stmt.loopMeasureNone, Bool.and_true]
      exact Block.hoistLoopPrefixInitsM_loopMeasureNone bss σ
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      simp only [Block.loopMeasureNone, Stmt.loopMeasureNone, Bool.and_true,
                 Block.hoistLoopPrefixInitsM_loopMeasureNone tss σ,
                 Block.hoistLoopPrefixInitsM_loopMeasureNone ess _]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      have h_body_mn :
          Block.loopMeasureNone (Block.hoistLoopPrefixInitsM body σ).1 =
            Block.loopMeasureNone body :=
        Block.hoistLoopPrefixInitsM_loopMeasureNone body σ
      have h_lift_mn :
          Block.loopMeasureNone
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 =
            Block.loopMeasureNone body := by
        rw [Block.liftInitsInLoopBodyM_snd_loopMeasureNone]; exact h_body_mn
      rw [Block.loopMeasureNone_append]
      simp only [Block.loopMeasureNone_map_cmd, Block.loopMeasureNone,
                 Stmt.loopMeasureNone, Bool.true_and, Bool.and_true]
      rw [Block.applyRenames_loopMeasureNone, h_lift_mn]
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  | .funcDecl d md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.loopMeasureNone, Stmt.loopMeasureNone]
  termination_by sizeOf s

private theorem Block.hoistLoopPrefixInitsM_loopMeasureNone
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.loopMeasureNone (Block.hoistLoopPrefixInitsM ss σ).1 =
      Block.loopMeasureNone ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInitsM, Block.loopMeasureNone]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.loopMeasureNone_append,
          Stmt.hoistLoopPrefixInitsM_loopMeasureNone s σ,
          Block.hoistLoopPrefixInitsM_loopMeasureNone rest _, Block.loopMeasureNone]
  termination_by sizeOf ss
end

/-- Top-level Phase 8 §B preservation (monadic fresh-name pass):
`Block.hoistLoopPrefixInits` preserves `Block.loopMeasureNone`. -/
theorem Block.hoistLoopPrefixInits_preserves_loopMeasureNone
    (ss : List (Stmt P (Cmd P)))
    (h : Block.loopMeasureNone ss = true) :
    Block.loopMeasureNone (Block.hoistLoopPrefixInits ss) = true := by
  rw [Block.hoistLoopPrefixInits, Block.hoistLoopPrefixInitsM_loopMeasureNone]
  exact h

/-! ### `simpleShape` is preserved by the pass

`simpleShape` is shape-only.  The lift leaves every `.loop` untouched (it does
not recurse into loops) and emits `.cmd (.set …)` residuals for hoisted inits
(`simpleShape = true`); `applyRenames` keeps a `.det e` guard `.det`
(`Block.applyRenames_simpleShape`); the fresh havoc prelude is all `.cmd`s.
Hence the whole pass preserves `simpleShape`.  Mirrors the `loopMeasureNone`
chain above. -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
private theorem Stmt.liftInitsInLoopBodyM_snd_simpleShape
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.simpleShape (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      Stmt.simpleShape s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.simpleShape, Stmt.simpleShape]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true]
      exact Block.liftInitsInLoopBodyM_snd_simpleShape bss σ
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      cases g with
      | det e =>
          simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true,
                     Block.liftInitsInLoopBodyM_snd_simpleShape tss σ,
                     Block.liftInitsInLoopBodyM_snd_simpleShape ess _]
      | nondet =>
          simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.simpleShape]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.simpleShape, Stmt.simpleShape]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.simpleShape, Stmt.simpleShape]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.simpleShape, Stmt.simpleShape]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBodyM_snd_simpleShape
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.simpleShape (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      Block.simpleShape ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.simpleShape]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual, Block.simpleShape_append,
          Stmt.liftInitsInLoopBodyM_snd_simpleShape s σ,
          Block.liftInitsInLoopBodyM_snd_simpleShape rest _, Block.simpleShape]
  termination_by sizeOf ss
end

mutual
private theorem Stmt.hoistLoopPrefixInitsM_simpleShape
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.simpleShape (Stmt.hoistLoopPrefixInitsM s σ).1 =
      Stmt.simpleShape s := by
  match s with
  | .cmd c =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.simpleShape, Stmt.simpleShape]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true]
      exact Block.hoistLoopPrefixInitsM_simpleShape bss σ
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      cases g with
      | det e =>
          simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true,
                     Block.hoistLoopPrefixInitsM_simpleShape tss σ,
                     Block.hoistLoopPrefixInitsM_simpleShape ess _]
      | nondet =>
          simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      have h_body_ss :
          Block.simpleShape (Block.hoistLoopPrefixInitsM body σ).1 =
            Block.simpleShape body :=
        Block.hoistLoopPrefixInitsM_simpleShape body σ
      have h_lift_ss :
          Block.simpleShape
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 =
            Block.simpleShape body := by
        rw [Block.liftInitsInLoopBodyM_snd_simpleShape]; exact h_body_ss
      have h_body₃_ss :
          Block.simpleShape
            (Block.applyRenames
              (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
              (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) =
            Block.simpleShape body := by
        rw [Block.applyRenames_simpleShape]; exact h_lift_ss
      rw [Block.simpleShape_append]
      cases g with
      | det e =>
          simp only [Block.simpleShape_map_cmd, Block.simpleShape,
                     Stmt.simpleShape, Bool.true_and, Bool.and_true, h_body₃_ss]
      | nondet =>
          simp only [Block.simpleShape_map_cmd, Block.simpleShape,
                     Stmt.simpleShape, Bool.true_and, Bool.and_true, h_body₃_ss]
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.simpleShape, Stmt.simpleShape]
  | .funcDecl d md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.simpleShape, Stmt.simpleShape]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.simpleShape, Stmt.simpleShape]
  termination_by sizeOf s

private theorem Block.hoistLoopPrefixInitsM_simpleShape
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.simpleShape (Block.hoistLoopPrefixInitsM ss σ).1 =
      Block.simpleShape ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInitsM, Block.simpleShape]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.simpleShape_append,
          Stmt.hoistLoopPrefixInitsM_simpleShape s σ,
          Block.hoistLoopPrefixInitsM_simpleShape rest _, Block.simpleShape]
  termination_by sizeOf ss
end

/-- Top-level: `Block.hoistLoopPrefixInits` preserves `Block.simpleShape`. -/
theorem Block.hoistLoopPrefixInits_preserves_simpleShape
    (ss : List (Stmt P (Cmd P)))
    (h : Block.simpleShape ss = true) :
    Block.simpleShape (Block.hoistLoopPrefixInits ss) = true := by
  rw [Block.hoistLoopPrefixInits, Block.hoistLoopPrefixInitsM_simpleShape]
  exact h

/-! ### `containsNondetLoop` / `containsFuncDecl` are preserved by the pass

Both are shape-only walkers; the lift never recurses into loops and emits only
`.cmd .init` havocs (no nondet loop, no funcDecl); `applyRenames` preserves
both walkers. So the whole pass preserves them in value. -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
private theorem Stmt.liftInitsInLoopBodyM_snd_containsNondetLoop
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.containsNondetLoop (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      Stmt.containsNondetLoop s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      simp only [Block.containsNondetLoop, Stmt.containsNondetLoop, Bool.or_false]
      exact Block.liftInitsInLoopBodyM_snd_containsNondetLoop bss σ
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      simp only [Block.containsNondetLoop, Stmt.containsNondetLoop, Bool.or_false,
                 Block.liftInitsInLoopBodyM_snd_containsNondetLoop tss σ,
                 Block.liftInitsInLoopBodyM_snd_containsNondetLoop ess _]
  | .loop g m inv body md =>
      cases g <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBodyM_snd_containsNondetLoop
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.containsNondetLoop (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      Block.containsNondetLoop ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.containsNondetLoop]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual, Block.containsNondetLoop_append,
          Stmt.liftInitsInLoopBodyM_snd_containsNondetLoop s σ,
          Block.liftInitsInLoopBodyM_snd_containsNondetLoop rest _, Block.containsNondetLoop]
  termination_by sizeOf ss
end

mutual
private theorem Stmt.hoistLoopPrefixInitsM_containsNondetLoop
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.containsNondetLoop (Stmt.hoistLoopPrefixInitsM s σ).1 =
      Stmt.containsNondetLoop s := by
  match s with
  | .cmd c =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.containsNondetLoop, Stmt.containsNondetLoop, Bool.or_false]
      exact Block.hoistLoopPrefixInitsM_containsNondetLoop bss σ
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      simp only [Block.containsNondetLoop, Stmt.containsNondetLoop, Bool.or_false,
                 Block.hoistLoopPrefixInitsM_containsNondetLoop tss σ,
                 Block.hoistLoopPrefixInitsM_containsNondetLoop ess _]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      have h_body :
          Block.containsNondetLoop (Block.hoistLoopPrefixInitsM body σ).1 =
            Block.containsNondetLoop body :=
        Block.hoistLoopPrefixInitsM_containsNondetLoop body σ
      have h_lift :
          Block.containsNondetLoop
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 =
            Block.containsNondetLoop body := by
        rw [Block.liftInitsInLoopBodyM_snd_containsNondetLoop]; exact h_body
      rw [Block.containsNondetLoop_append]
      simp only [Block.containsNondetLoop_map_cmd, Block.containsNondetLoop,
                 Bool.false_or, Bool.or_false]
      cases g <;>
        simp only [Stmt.containsNondetLoop, Block.applyRenames_containsNondetLoop, h_lift]
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  | .funcDecl d md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.containsNondetLoop, Stmt.containsNondetLoop]
  termination_by sizeOf s

private theorem Block.hoistLoopPrefixInitsM_containsNondetLoop
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.containsNondetLoop (Block.hoistLoopPrefixInitsM ss σ).1 =
      Block.containsNondetLoop ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInitsM, Block.containsNondetLoop]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.containsNondetLoop_append,
          Stmt.hoistLoopPrefixInitsM_containsNondetLoop s σ,
          Block.hoistLoopPrefixInitsM_containsNondetLoop rest _, Block.containsNondetLoop]
  termination_by sizeOf ss
end

/-- The pass preserves `containsNondetLoop` in value. -/
theorem Block.hoistLoopPrefixInits_containsNondetLoop_eq
    (ss : List (Stmt P (Cmd P))) :
    Block.containsNondetLoop (Block.hoistLoopPrefixInits ss) =
      Block.containsNondetLoop ss := by
  rw [Block.hoistLoopPrefixInits, Block.hoistLoopPrefixInitsM_containsNondetLoop]

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
private theorem Stmt.liftInitsInLoopBodyM_snd_containsFuncDecl
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.containsFuncDecl (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      Stmt.containsFuncDecl s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      simp only [Block.containsFuncDecl, Stmt.containsFuncDecl, Bool.or_false]
      exact Block.liftInitsInLoopBodyM_snd_containsFuncDecl bss σ
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      simp only [Block.containsFuncDecl, Stmt.containsFuncDecl, Bool.or_false,
                 Block.liftInitsInLoopBodyM_snd_containsFuncDecl tss σ,
                 Block.liftInitsInLoopBodyM_snd_containsFuncDecl ess _]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBodyM_snd_containsFuncDecl
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.containsFuncDecl (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      Block.containsFuncDecl ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.containsFuncDecl]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual, Block.containsFuncDecl_append,
          Stmt.liftInitsInLoopBodyM_snd_containsFuncDecl s σ,
          Block.liftInitsInLoopBodyM_snd_containsFuncDecl rest _, Block.containsFuncDecl]
  termination_by sizeOf ss
end

mutual
private theorem Stmt.hoistLoopPrefixInitsM_containsFuncDecl
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.containsFuncDecl (Stmt.hoistLoopPrefixInitsM s σ).1 =
      Stmt.containsFuncDecl s := by
  match s with
  | .cmd c =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.containsFuncDecl, Stmt.containsFuncDecl, Bool.or_false]
      exact Block.hoistLoopPrefixInitsM_containsFuncDecl bss σ
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      simp only [Block.containsFuncDecl, Stmt.containsFuncDecl, Bool.or_false,
                 Block.hoistLoopPrefixInitsM_containsFuncDecl tss σ,
                 Block.hoistLoopPrefixInitsM_containsFuncDecl ess _]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      have h_body :
          Block.containsFuncDecl (Block.hoistLoopPrefixInitsM body σ).1 =
            Block.containsFuncDecl body :=
        Block.hoistLoopPrefixInitsM_containsFuncDecl body σ
      have h_lift :
          Block.containsFuncDecl
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 =
            Block.containsFuncDecl body := by
        rw [Block.liftInitsInLoopBodyM_snd_containsFuncDecl]; exact h_body
      rw [Block.containsFuncDecl_append]
      simp only [Block.containsFuncDecl_map_cmd, Block.containsFuncDecl,
                 Stmt.containsFuncDecl, Bool.false_or, Bool.or_false]
      rw [Block.applyRenames_containsFuncDecl, h_lift]
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  | .funcDecl d md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.containsFuncDecl, Stmt.containsFuncDecl]
  termination_by sizeOf s

private theorem Block.hoistLoopPrefixInitsM_containsFuncDecl
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.containsFuncDecl (Block.hoistLoopPrefixInitsM ss σ).1 =
      Block.containsFuncDecl ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInitsM, Block.containsFuncDecl]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.containsFuncDecl_append,
          Stmt.hoistLoopPrefixInitsM_containsFuncDecl s σ,
          Block.hoistLoopPrefixInitsM_containsFuncDecl rest _, Block.containsFuncDecl]
  termination_by sizeOf ss
end

/-- The pass preserves `containsFuncDecl` in value. -/
theorem Block.hoistLoopPrefixInits_containsFuncDecl_eq
    (ss : List (Stmt P (Cmd P))) :
    Block.containsFuncDecl (Block.hoistLoopPrefixInits ss) =
      Block.containsFuncDecl ss := by
  rw [Block.hoistLoopPrefixInits, Block.hoistLoopPrefixInitsM_containsFuncDecl]

/-! ### `loopHasNoInvariants` is preserved by the pass -/

omit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] in
mutual
private theorem Stmt.liftInitsInLoopBodyM_snd_loopHasNoInvariants
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.loopHasNoInvariants (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      Stmt.loopHasNoInvariants s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true]
      exact Block.liftInitsInLoopBodyM_snd_loopHasNoInvariants bss σ
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true,
                 Block.liftInitsInLoopBodyM_snd_loopHasNoInvariants tss σ,
                 Block.liftInitsInLoopBodyM_snd_loopHasNoInvariants ess _]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBodyM_snd_loopHasNoInvariants
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.loopHasNoInvariants (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      Block.loopHasNoInvariants ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.loopHasNoInvariants]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual, Block.loopHasNoInvariants_append,
          Stmt.liftInitsInLoopBodyM_snd_loopHasNoInvariants s σ,
          Block.liftInitsInLoopBodyM_snd_loopHasNoInvariants rest _, Block.loopHasNoInvariants]
  termination_by sizeOf ss
end

mutual
private theorem Stmt.hoistLoopPrefixInitsM_loopHasNoInvariants
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.loopHasNoInvariants (Stmt.hoistLoopPrefixInitsM s σ).1 =
      Stmt.loopHasNoInvariants s := by
  match s with
  | .cmd c =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true]
      exact Block.hoistLoopPrefixInitsM_loopHasNoInvariants bss σ
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true,
                 Block.hoistLoopPrefixInitsM_loopHasNoInvariants tss σ,
                 Block.hoistLoopPrefixInitsM_loopHasNoInvariants ess _]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      have h_body :
          Block.loopHasNoInvariants (Block.hoistLoopPrefixInitsM body σ).1 =
            Block.loopHasNoInvariants body :=
        Block.hoistLoopPrefixInitsM_loopHasNoInvariants body σ
      have h_lift :
          Block.loopHasNoInvariants
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 =
            Block.loopHasNoInvariants body := by
        rw [Block.liftInitsInLoopBodyM_snd_loopHasNoInvariants]; exact h_body
      rw [Block.loopHasNoInvariants_append]
      simp only [Block.loopHasNoInvariants_map_cmd, Block.loopHasNoInvariants,
                 Stmt.loopHasNoInvariants, Bool.true_and, Bool.and_true]
      rw [Block.applyRenames_loopHasNoInvariants, h_lift]
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .funcDecl d md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  termination_by sizeOf s

private theorem Block.hoistLoopPrefixInitsM_loopHasNoInvariants
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.loopHasNoInvariants (Block.hoistLoopPrefixInitsM ss σ).1 =
      Block.loopHasNoInvariants ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInitsM, Block.loopHasNoInvariants]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.loopHasNoInvariants_append,
          Stmt.hoistLoopPrefixInitsM_loopHasNoInvariants s σ,
          Block.hoistLoopPrefixInitsM_loopHasNoInvariants rest _, Block.loopHasNoInvariants]
  termination_by sizeOf ss
end

/-- The pass preserves `loopHasNoInvariants` in value. -/
theorem Block.hoistLoopPrefixInits_loopHasNoInvariants_eq
    (ss : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (Block.hoistLoopPrefixInits ss) =
      Block.loopHasNoInvariants ss := by
  rw [Block.hoistLoopPrefixInits, Block.hoistLoopPrefixInitsM_loopHasNoInvariants]

end MonadicPostconds

end Imperative
