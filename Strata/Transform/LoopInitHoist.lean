/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtProps
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Util.LabelGen

public section

namespace Imperative

open LabelGen (StringGenM)

/-! # `hoistLoopPrefixInits` — structured-to-structured loop-init hoist

A pass that transforms a `List (Stmt P (Cmd P))` so that every `.loop` body
contains no `.init` commands at any nesting level. Concretely, the output
satisfies `Block.loopBodyNoInits = true`.

**Same-name lift (pure, no rename).**

Strategy (post-order traversal): at every `.loop _ _ _ body _`, recurse into
`body` first (so nested loops are already hoist-processed), then call
`liftInitsInLoopBody` to walk the body and collect every `.init` reachable
through `.block` and `.ite` substructures (but not into nested loops, which are
already processed). Each collected init `init y ty rhs md` is lifted to a
SAME-name prelude havoc `init y ty .nondet md` emitted as a SIBLING before the
rewritten loop, and the body init is rewritten in place to `set y rhs md`. No
fresh name is generated and no substitution is applied — soundness rests on the
`StoreAgreement` pipeline relation ignoring source-undefined slots, gated by
`Block.uniqueInits`.

This file keeps the pure same-name pass definitions plus the shape-independent
helper lemmas consumed by the downstream proof files. The measure-free-loop
precondition they use is `Block.noMeasureLoops` from `Stmt.lean`.
-/

/-- The fixed prefix carried by the hoist's `hoistKind` label classification in
`LoopInitHoistCorrect` (the same-name pass here generates no names of its own).
`hoistKind` uses it to recognise "a label some hoist generator could have
produced"; uniqueness of any such label comes from the underlying
`StringGenState` counter, not from the prefix, which only makes generated names
human-recognisable. -/
@[expose] def hoistFreshPrefix : String := "$__hoist$"

/-! ## Same-name lift and hoist (pure, no rename)

The pipeline relation is `StoreAgreement` (source-on-left), which constrains
only source-*defined* slots, so it ignores the post-iteration divergence where
the source pops a body-local `y` to `none` while the hoisted prelude keeps it
defined. Reuse of the source name `y` is therefore sound, gated by
`Block.uniqueInits` (global init-name `Nodup`, carried in `PipelinePre`), which
rules out two hoisted preludes colliding.

These same-name variants are pure (`Block → Block`, no `StringGenM`): the
`.init y ty rhs md` case lifts to a prelude havoc `init y ty .nondet md` (SAME
`y`), rewrites the body init to `set y rhs md`, and records no rename — so no
renaming/substitution step is needed. -/

mutual
/-- Same-name lift of a loop body: collect every `.init` at any depth and lift
it to a SAME-name prelude havoc. Does NOT recurse into nested `.loop`
substructures (already hoist-processed in post-order).

Returns a pair `(havocs, body')`:
* `havocs` is the list of prelude commands `init y ty .nondet md` (SAME lhs `y`,
  havoc rhs), and
* `body'` is `s` with each lifted init rewritten as `Cmd.set y rhs md` (SAME
  name `y`; no rename pair, no substitution). -/
@[expose] def Stmt.liftInitsInLoopBody {P : PureExpr}
    (s : Stmt P (Cmd P)) :
    List (Cmd P) × List (Stmt P (Cmd P)) :=
  match s with
  | .cmd (.init y ty rhs md) =>
      ([.init y ty .nondet md], [.cmd (.set y rhs md)])
  | .cmd c => ([], [.cmd c])
  | .block lbl bss md =>
      let (hs, bss') := Block.liftInitsInLoopBody bss
      (hs, [.block lbl bss' md])
  | .ite g tss ess md =>
      let (ths, tss') := Block.liftInitsInLoopBody tss
      let (ehs, ess') := Block.liftInitsInLoopBody ess
      (ths ++ ehs, [.ite g tss' ess' md])
  | .loop g m inv body md => ([], [.loop g m inv body md])
  | .exit lbl md => ([], [.exit lbl md])
  | .funcDecl d md => ([], [.funcDecl d md])
  | .typeDecl t md => ([], [.typeDecl t md])
  termination_by sizeOf s

/-- Apply `Stmt.liftInitsInLoopBody` to every statement in the block,
concatenating the harvested havocs and rewritten residuals. -/
@[expose] def Block.liftInitsInLoopBody {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) :
    List (Cmd P) × List (Stmt P (Cmd P)) :=
  match ss with
  | [] => ([], [])
  | s :: rest =>
      let (hs_s, ss_s) := Stmt.liftInitsInLoopBody s
      let (hs_r, ss_r) := Block.liftInitsInLoopBody rest
      (hs_s ++ hs_r, ss_s ++ ss_r)
  termination_by sizeOf ss
end

mutual
/-- Same-name top-level pass (pure): post-order traversal. For a `.loop`,
recurse into the body first (so nested loops are hoist-processed), then call
`Block.liftInitsInLoopBody` on the post-processed body to collect this loop's
body inits with their SAME names. The havocs are emitted as SIBLING commands
*before* the rewritten loop; the body is NOT renamed (same names). For `.block`
and `.ite`, recurse structurally. Other statements are identity. -/
@[expose] def Stmt.hoistLoopPrefixInits {P : PureExpr}
    (s : Stmt P (Cmd P)) : List (Stmt P (Cmd P)) :=
  match s with
  | .cmd c => [.cmd c]
  | .block lbl bss md => [.block lbl (Block.hoistLoopPrefixInits bss) md]
  | .ite g tss ess md =>
      [.ite g (Block.hoistLoopPrefixInits tss) (Block.hoistLoopPrefixInits ess) md]
  | .loop g m inv body md =>
      let body₁ := Block.hoistLoopPrefixInits body
      let (havocs, body₂) := Block.liftInitsInLoopBody body₁
      havocs.map Stmt.cmd ++ [.loop g m inv body₂ md]
  | .exit lbl md => [.exit lbl md]
  | .funcDecl d md => [.funcDecl d md]
  | .typeDecl t md => [.typeDecl t md]
  termination_by sizeOf s

/-- Apply `Stmt.hoistLoopPrefixInits` to each statement of the block,
concatenating the resulting lists. -/
@[expose] def Block.hoistLoopPrefixInits {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) : List (Stmt P (Cmd P)) :=
  match ss with
  | [] => []
  | s :: rest => Stmt.hoistLoopPrefixInits s ++ Block.hoistLoopPrefixInits rest
  termination_by sizeOf ss
end

/-! ## Shape-independent helper lemmas

These distribute the structural Bool walkers over `++` and assert their
triviality on `.cmd`-only prelude lists. They do not mention the hoist pass
itself and are consumed by the downstream proof files. -/

/-- A list of non-init `.cmd`s contributes trivially to
`Block.loopBodyNoInits`. -/
private theorem Block.loopBodyNoInits_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.loopBodyNoInits (cs.map Stmt.cmd) = true := by
  induction cs with
  | nil => simp [Block.loopBodyNoInits]
  | cons c rest ih =>
    simp [List.map_cons, Block.loopBodyNoInits,
          Stmt.loopBodyNoInits, ih]

/-- A list of `.cmd`s trivially has `simpleShape = true`. -/
private theorem Block.simpleShape_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.simpleShape (cs.map Stmt.cmd) = true := by
  induction cs with
  | nil => simp [Block.simpleShape]
  | cons c rest ih =>
    simp [List.map_cons, Block.simpleShape, Stmt.simpleShape, ih]

/-- A list of `.cmd`s trivially has `loopHasNoInvariants = true`. -/
private theorem Block.loopHasNoInvariants_map_cmd {P : PureExpr}
    (cs : List (Cmd P)) :
    Block.loopHasNoInvariants (cs.map Stmt.cmd : List (Stmt P (Cmd P))) = true := by
  induction cs with
  | nil => simp [Block.loopHasNoInvariants]
  | cons c rest ih =>
    simp [List.map_cons, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, ih]

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

mutual
/-- Empty deep `initVars` list ⇒ no inits anywhere (converse of
`initVars_eq_nil_of_noInitsAnywhere`). -/
theorem Stmt.noInitsAnywhere_of_initVars_nil
    (s : Stmt P (Cmd P)) (h : Stmt.initVars s = []) :
    Stmt.noInitsAnywhere s = true := by
  match s with
  | .cmd c => cases c <;> simp_all [Stmt.noInitsAnywhere, Stmt.initVars]
  | .block lbl bss md =>
      rw [Stmt.initVars_block] at h; simp only [Stmt.noInitsAnywhere]
      exact Block.noInitsAnywhere_of_initVars_nil bss h
  | .ite g tss ess md =>
      rw [Stmt.initVars_ite, List.append_eq_nil_iff] at h
      simp only [Stmt.noInitsAnywhere,
        Block.noInitsAnywhere_of_initVars_nil tss h.1,
        Block.noInitsAnywhere_of_initVars_nil ess h.2, Bool.and_true]
  | .loop g m inv bss md =>
      rw [Stmt.initVars_loop] at h; simp only [Stmt.noInitsAnywhere]
      exact Block.noInitsAnywhere_of_initVars_nil bss h
  | .exit lbl md => simp [Stmt.noInitsAnywhere]
  | .funcDecl d md => simp [Stmt.noInitsAnywhere]
  | .typeDecl t md => simp [Stmt.noInitsAnywhere]
  termination_by sizeOf s

theorem Block.noInitsAnywhere_of_initVars_nil
    (ss : List (Stmt P (Cmd P))) (h : Block.initVars ss = []) :
    Block.noInitsAnywhere ss = true := by
  match ss with
  | [] => simp [Block.noInitsAnywhere]
  | s :: rest =>
      rw [Block.initVars_cons, List.append_eq_nil_iff] at h
      simp only [Block.noInitsAnywhere,
        Stmt.noInitsAnywhere_of_initVars_nil s h.1,
        Block.noInitsAnywhere_of_initVars_nil rest h.2, Bool.and_true]
  termination_by sizeOf ss
end

/-- On any block, `(Block.initVars ss).isEmpty = Block.noInitsAnywhere ss`:
both walk the same tree and `.init` is the sole producer of an `initVars`
entry. -/
theorem Block.isEmpty_initVars_eq_noInitsAnywhere
    (ss : List (Stmt P (Cmd P))) :
    (Block.initVars ss).isEmpty = Block.noInitsAnywhere ss := by
  rcases he : (Block.initVars ss).isEmpty with _ | _
  · symm
    rw [Bool.eq_false_iff, Ne]
    intro hn
    rw [Block.initVars_eq_nil_of_noInitsAnywhere ss hn] at he
    simp at he
  · symm
    rw [List.isEmpty_iff] at he
    exact Block.noInitsAnywhere_of_initVars_nil ss he

end Imperative
