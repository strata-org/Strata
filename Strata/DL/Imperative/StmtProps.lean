/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Util.StringGen
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Util.ListUtils

namespace Imperative

public section

variable {P : PureExpr} {C : Type}

/-! # Metatheory of the statement-language shape predicates

Equational theory for the boolean shape walkers defined in
`Strata.DL.Imperative.Stmt`. Key results, by group:

- Disjointness of `funcDeclNames` from `definedVars`/`declared`
  (`Stmt`/`Block.funcDeclNames_disjoint_of_defined`/`_of_declared`,
  `funcDeclNames_eq_nil_of_noFuncDecl`).
- Per-constructor decomposition lemmas for `simpleShape`, `loopBodyNoInits`,
  `loopHasNoInvariants`, `noMeasureLoops`, `initVars`, `exitsCoveredByBlocks`,
  and `getBlockLabels` (the `_cons_iff` / `_branch_*` / `_loop_*` / `_block_*`
  families), plus the two non-structural results `exitsCoveredByBlocks_weaken`
  (label-list monotonicity) and `all_cmd_exitsCoveredByBlocks`.
- Distribution of the block-level walkers over `++`
  (`initVars`/`simpleShape`/`loopHasNoInvariants`/`modifiedVars`/
  `noInitsAnywhere`/`loopBodyNoInits`/`getBlockLabels`_append).
- Under `noFuncDecl`, defined variables coincide with init variables
  (`Stmt`/`Block.definedVars_eq_initVars_of_noFuncDecl`), the block-to-statement
  non-membership projection `all_not_mem_definedVars_of_block`, and the
  init-⊆-defined inclusion (`Stmt`/`Block.mem_initVars_mem_definedVars`).
-/

/-! ### Disjointness of funcDeclNames from definedVars

The strengthened `defUseWellFormed.funcDecl` case requires that each
`funcDecl decl _` AST node satisfies `!definedVars decl.name` at its
position.  This lets us derive: every name in `funcDeclNames s` is NOT
in the initial `definedVars` predicate.  Used by simulation proofs
when combined with `block_preserves_eval_on_disjoint`.
-/

mutual

theorem Stmt.funcDeclNames_disjoint_of_defined [HasVarsImp P C]
    [HasFvars P] [HasOps P] [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (defined : P.Ident → Bool) (declared : P.Ident → Bool) (s : Stmt P C)
    (hwf : Stmt.defUseWellFormed defined declared s = true) :
    ∀ n ∈ Stmt.funcDeclNames s false, defined n = false := by
  match s with
  | .cmd _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .exit _ _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .typeDecl _ _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .funcDecl decl _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    subst hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    exact Bool.not_eq_true _ |>.mp (by simpa using hwf.1.1.2)
  | .block _ bss _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    simp [Stmt.defUseWellFormed] at hwf
    exact Block.funcDeclNames_disjoint_of_defined defined declared bss hwf n hn
  | .ite _ tss ess _ =>
    intro n hn
    simp [Stmt.funcDeclNames, List.mem_append] at hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    rcases hn with hn | hn
    · exact Block.funcDeclNames_disjoint_of_defined defined declared tss hwf.1.2 n hn
    · exact Block.funcDeclNames_disjoint_of_defined defined declared ess hwf.2 n hn
  | .loop _ _ _ body _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    exact Block.funcDeclNames_disjoint_of_defined defined declared body hwf.2 n hn

theorem Block.funcDeclNames_disjoint_of_defined [HasVarsImp P C]
    [HasFvars P] [HasOps P] [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (defined : P.Ident → Bool) (declared : P.Ident → Bool) (bss : Block P C)
    (hwf : Block.defUseWellFormed defined declared bss = true) :
    ∀ n ∈ Block.funcDeclNames bss false, defined n = false := by
  match bss with
  | [] => intro n hn; simp [Block.funcDeclNames] at hn
  | s :: rest =>
    intro n hn
    simp [Block.funcDeclNames, List.mem_append] at hn
    simp [Block.defUseWellFormed, Bool.and_eq_true] at hwf
    rcases hn with hn | hn
    · exact Stmt.funcDeclNames_disjoint_of_defined defined declared s hwf.1 n hn
    · -- The tail's predicate is `definedVars ∪ definedVars(s)`; if `n` is in
      -- `funcDeclNames rest`, then it's not in the larger predicate, hence
      -- not in `definedVars` either.
      have ih := Block.funcDeclNames_disjoint_of_defined
        (fun m => defined m || decide (m ∈ Stmt.definedVars s true))
        (fun m => declared m || decide (m ∈ Stmt.funcDeclNames s true)) rest hwf.2 n hn
      simp [Bool.or_eq_false_iff] at ih
      exact ih.1

end

mutual

/-- All `funcDeclNames` of `s` are *not* in the initial `declared` predicate,
    given `Stmt.defUseWellFormed defined declared s = true`.  This is the
    operator-level analog of `Stmt.funcDeclNames_disjoint_of_defined`. -/
theorem Stmt.funcDeclNames_disjoint_of_declared [HasVarsImp P C]
    [HasFvars P] [HasOps P] [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (defined : P.Ident → Bool) (declared : P.Ident → Bool) (s : Stmt P C)
    (hwf : Stmt.defUseWellFormed defined declared s = true) :
    ∀ n ∈ Stmt.funcDeclNames s false, declared n = false := by
  match s with
  | .cmd _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .exit _ _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .typeDecl _ _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .funcDecl decl _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    subst hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    exact Bool.not_eq_true _ |>.mp (by simpa using hwf.2)
  | .block _ bss _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    simp [Stmt.defUseWellFormed] at hwf
    exact Block.funcDeclNames_disjoint_of_declared defined declared bss hwf n hn
  | .ite _ tss ess _ =>
    intro n hn
    simp [Stmt.funcDeclNames, List.mem_append] at hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    rcases hn with hn | hn
    · exact Block.funcDeclNames_disjoint_of_declared defined declared tss hwf.1.2 n hn
    · exact Block.funcDeclNames_disjoint_of_declared defined declared ess hwf.2 n hn
  | .loop _ _ _ body _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    exact Block.funcDeclNames_disjoint_of_declared defined declared body hwf.2 n hn

theorem Block.funcDeclNames_disjoint_of_declared [HasVarsImp P C]
    [HasFvars P] [HasOps P] [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (defined : P.Ident → Bool) (declared : P.Ident → Bool) (bss : Block P C)
    (hwf : Block.defUseWellFormed defined declared bss = true) :
    ∀ n ∈ Block.funcDeclNames bss false, declared n = false := by
  match bss with
  | [] => intro n hn; simp [Block.funcDeclNames] at hn
  | s :: rest =>
    intro n hn
    simp [Block.funcDeclNames, List.mem_append] at hn
    simp [Block.defUseWellFormed, Bool.and_eq_true] at hwf
    rcases hn with hn | hn
    · exact Stmt.funcDeclNames_disjoint_of_declared defined declared s hwf.1 n hn
    · have ih := Block.funcDeclNames_disjoint_of_declared
        (fun m => defined m || decide (m ∈ Stmt.definedVars s true))
        (fun m => declared m || decide (m ∈ Stmt.funcDeclNames s true)) rest hwf.2 n hn
      simp [Bool.or_eq_false_iff] at ih
      exact ih.1

end

mutual

/-- If a statement contains no function declarations, then `funcDeclNames` is
    empty (for either choice of `excludeScoped`). -/
theorem Stmt.funcDeclNames_eq_nil_of_noFuncDecl
    (s : Stmt P C) (excludeScoped : Bool) (h : Stmt.noFuncDecl s = true) :
    Stmt.funcDeclNames s excludeScoped = [] := by
  match s with
  | .cmd _ => simp [Stmt.funcDeclNames]
  | .exit _ _ => simp [Stmt.funcDeclNames]
  | .typeDecl _ _ => simp [Stmt.funcDeclNames]
  | .funcDecl _ _ => simp [Stmt.noFuncDecl] at h
  | .block _ bss _ =>
    simp [Stmt.noFuncDecl] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    exact Block.funcDeclNames_eq_nil_of_noFuncDecl bss false h
  | .ite _ tss ess _ =>
    simp [Stmt.noFuncDecl, Bool.and_eq_true] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    refine ⟨?_, ?_⟩
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl tss false h.1
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl ess false h.2
  | .loop _ _ _ body _ =>
    simp [Stmt.noFuncDecl] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    exact Block.funcDeclNames_eq_nil_of_noFuncDecl body false h

/-- If a block contains no function declarations, then `funcDeclNames` is empty. -/
theorem Block.funcDeclNames_eq_nil_of_noFuncDecl
    (ss : Block P C) (excludeScoped : Bool) (h : Block.noFuncDecl ss = true) :
    Block.funcDeclNames ss excludeScoped = [] := by
  match ss with
  | [] => simp [Block.funcDeclNames]
  | s :: rest =>
    simp [Block.noFuncDecl, Bool.and_eq_true] at h
    simp [Block.funcDeclNames]
    refine ⟨?_, ?_⟩
    · exact Stmt.funcDeclNames_eq_nil_of_noFuncDecl s excludeScoped h.1
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl rest excludeScoped h.2

end

/-! ### Decomposition lemmas for the structural shape predicates

Per-constructor unfolding lemmas for `simpleShape`, `loopBodyNoInits`,
`loopHasNoInvariants`, `noMeasureLoops`, `initVars`, `exitsCoveredByBlocks`,
and `getBlockLabels`.  They accompany the `_append` distribution lemmas
below; the transform correctness proofs consume both.  The predicates
themselves are defined in `Strata.DL.Imperative.Stmt`. -/

/-- `Block.simpleShape` on `s :: rest` decomposes to the conjunction. -/
theorem Block.simpleShape_cons_iff
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
    Block.simpleShape (s :: rest) = true ↔
      Stmt.simpleShape s = true ∧ Block.simpleShape rest = true := by
  simp only [Block.simpleShape, Bool.and_eq_true]

/-- The then-branch of an `.ite (.det _)` is simple when the whole ite is. -/
theorem Stmt.simpleShape_branch_then
    {g : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.simpleShape (.ite (.det g) tss ess md) = true →
    Block.simpleShape tss = true := by
  simp only [Stmt.simpleShape, Bool.and_eq_true]
  intro h
  exact h.1

/-- The else-branch of an `.ite (.det _)` is simple when the whole ite is. -/
theorem Stmt.simpleShape_branch_else
    {g : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.simpleShape (.ite (.det g) tss ess md) = true →
    Block.simpleShape ess = true := by
  simp only [Stmt.simpleShape, Bool.and_eq_true]
  intro h
  exact h.2

/-- The body of a `.loop` is simple when the whole loop-statement is. -/
theorem Stmt.simpleShape_loop_body
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.simpleShape (.loop g m is body md) = true →
    Block.simpleShape body = true := by
  intro h
  unfold Stmt.simpleShape at h
  cases g with
  | det ge => simpa using h
  | nondet => simp at h

/-- The guard of a simple-shape `.loop` is deterministic. -/
theorem Stmt.simpleShape_loop_guard_det
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.simpleShape (.loop g m is body md) = true →
    ∃ ge, g = .det ge := by
  intro h
  unfold Stmt.simpleShape at h
  cases g with
  | det ge => exact ⟨ge, rfl⟩
  | nondet => simp at h

theorem Block.loopBodyNoInits_cons_iff
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
    Block.loopBodyNoInits (s :: rest) = true ↔
      Stmt.loopBodyNoInits s = true ∧ Block.loopBodyNoInits rest = true := by
  simp only [Block.loopBodyNoInits, Bool.and_eq_true]

theorem Stmt.loopBodyNoInits_branch_then
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopBodyNoInits (.ite g tss ess md) = true →
    Block.loopBodyNoInits tss = true := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true]
  intro h; exact h.1

theorem Stmt.loopBodyNoInits_branch_else
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopBodyNoInits (.ite g tss ess md) = true →
    Block.loopBodyNoInits ess = true := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true]
  intro h; exact h.2

theorem Stmt.loopBodyNoInits_block_body
    {label : String} {body : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopBodyNoInits (.block label body md) = true →
    Block.loopBodyNoInits body = true := by
  simp only [Stmt.loopBodyNoInits]
  intro h; exact h

/-- A loop's body has no local variable initializations. -/
theorem Stmt.loopBodyNoInits_loop_body
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.loopBodyNoInits (.loop g m is body md) = true →
    Block.initVars body = [] := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true, List.isEmpty_iff]
  intro h; exact h.1

/-- The recursive `loopBodyNoInits` discharge for a loop's body. -/
theorem Stmt.loopBodyNoInits_loop_body_rec
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.loopBodyNoInits (.loop g m is body md) = true →
    Block.loopBodyNoInits body = true := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true]
  intro h; exact h.2

theorem Block.loopHasNoInvariants_cons_iff
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
    Block.loopHasNoInvariants (s :: rest) = true ↔
      Stmt.loopHasNoInvariants s = true ∧ Block.loopHasNoInvariants rest = true := by
  simp only [Block.loopHasNoInvariants, Bool.and_eq_true]

theorem Stmt.loopHasNoInvariants_branch_then
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopHasNoInvariants (.ite g tss ess md) = true →
    Block.loopHasNoInvariants tss = true := by
  simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true]
  intro h; exact h.1

theorem Stmt.loopHasNoInvariants_branch_else
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopHasNoInvariants (.ite g tss ess md) = true →
    Block.loopHasNoInvariants ess = true := by
  simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true]
  intro h; exact h.2

theorem Stmt.loopHasNoInvariants_block_body
    {label : String} {body : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.loopHasNoInvariants (.block label body md) = true →
    Block.loopHasNoInvariants body = true := by
  simp only [Stmt.loopHasNoInvariants]
  intro h; exact h

/-- A loop has no labeled invariants. -/
theorem Stmt.loopHasNoInvariants_loop_invs
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.loopHasNoInvariants (.loop g m is body md) = true →
    is = [] := by
  simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true, List.isEmpty_iff]
  intro h; exact h.1

/-- The recursive `loopHasNoInvariants` discharge for a loop's body. -/
theorem Stmt.loopHasNoInvariants_loop_body_rec
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.loopHasNoInvariants (.loop g m is body md) = true →
    Block.loopHasNoInvariants body = true := by
  simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true]
  intro h; exact h.2

theorem Block.noMeasureLoops_cons_iff
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
    Block.noMeasureLoops (s :: rest) = true ↔
      Stmt.noMeasureLoops s = true ∧ Block.noMeasureLoops rest = true := by
  simp only [Block.noMeasureLoops, Bool.and_eq_true]

theorem Stmt.noMeasureLoops_branch_then
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.noMeasureLoops (.ite g tss ess md) = true →
    Block.noMeasureLoops tss = true := by
  simp only [Stmt.noMeasureLoops, Bool.and_eq_true]
  intro h; exact h.1

theorem Stmt.noMeasureLoops_branch_else
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.noMeasureLoops (.ite g tss ess md) = true →
    Block.noMeasureLoops ess = true := by
  simp only [Stmt.noMeasureLoops, Bool.and_eq_true]
  intro h; exact h.2

theorem Stmt.noMeasureLoops_block_body
    {label : String} {body : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.noMeasureLoops (.block label body md) = true →
    Block.noMeasureLoops body = true := by
  simp only [Stmt.noMeasureLoops]
  intro h; exact h

/-- The recursive `noMeasureLoops` discharge for a loop's body. -/
theorem Stmt.noMeasureLoops_loop_body_rec
    {g : ExprOrNondet P} {m : Option P.Expr}
    {is : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} :
    Stmt.noMeasureLoops (.loop g m is body md) = true →
    Block.noMeasureLoops body = true := by
  simp only [Stmt.noMeasureLoops, Bool.and_eq_true]
  intro h; exact h.2

/-! #### Decomposition helpers for `initVars`

`Block.initVars`/`Stmt.initVars` are fully transitive: they recurse through
`.block`/`.ite`/`.loop` bodies and enumerate EVERY `.init` declaration at
every nesting depth (see the mutual definitions in `Stmt.lean`). The lemmas
below are all definitional unfoldings (`rfl`) but stated as named lemmas so
proofs can `rw` against them without unfolding the whole mutual block. -/

/-- Cons-decomposition of `Block.initVars`. -/
@[simp] theorem Block.initVars_cons {P : PureExpr}
    (s : Stmt P (Cmd P)) (ss : List (Stmt P (Cmd P))) :
    Block.initVars (s :: ss) =
      Stmt.initVars s ++ Block.initVars ss := by
  simp [Block.initVars]

/-- `Stmt.initVars` on `.loop` is its body's deep init list. -/
@[simp] theorem Stmt.initVars_loop {P : PureExpr}
    (g : ExprOrNondet P) (m : Option P.Expr)
    (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P) :
    Stmt.initVars (.loop g m inv body md) =
      Block.initVars body := by
  simp [Stmt.initVars]

/-- `Stmt.initVars` on `.block` is its body's deep init list. -/
@[simp] theorem Stmt.initVars_block {P : PureExpr}
    (lbl : String) (ss : List (Stmt P (Cmd P))) (md : MetaData P) :
    Stmt.initVars (.block lbl ss md) =
      Block.initVars ss := by
  simp [Stmt.initVars]

/-- `Stmt.initVars` on `.ite` is the concatenation of both branches' deep
init lists. -/
@[simp] theorem Stmt.initVars_ite {P : PureExpr}
    (c : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) :
    Stmt.initVars (.ite c tss ess md) =
      Block.initVars tss ++ Block.initVars ess := by
  simp [Stmt.initVars]

theorem block_exitsCoveredByBlocks_append
    {P : PureExpr} {CmdT : Type}
    (labels : List String) (ss₁ ss₂ : List (Stmt P CmdT))
    (h₁ : Block.exitsCoveredByBlocks labels ss₁)
    (h₂ : Block.exitsCoveredByBlocks labels ss₂) :
    Block.exitsCoveredByBlocks labels (ss₁ ++ ss₂) := by
  induction ss₁ with
  | nil => exact h₂
  | cons s ss ih => exact ⟨h₁.1, ih h₁.2⟩

/-- `exitsCoveredByBlocks` is monotone in the label list: more covering labels
    can only help. -/
theorem exitsCoveredByBlocks_weaken
    {P : PureExpr} {CmdT : Type}
    (labels₁ labels₂ : List String)
    (hsub : ∀ l, l ∈ labels₁ → l ∈ labels₂) :
    (∀ (s : Stmt P CmdT),
      s.exitsCoveredByBlocks labels₁ → s.exitsCoveredByBlocks labels₂) ∧
    (∀ (ss : List (Stmt P CmdT)),
      Block.exitsCoveredByBlocks labels₁ ss →
      Block.exitsCoveredByBlocks labels₂ ss) := by
  suffices hstmt : ∀ (s : Stmt P CmdT),
      ∀ labels₁ labels₂, (∀ l, l ∈ labels₁ → l ∈ labels₂) →
        s.exitsCoveredByBlocks labels₁ → s.exitsCoveredByBlocks labels₂ by
    constructor
    · exact fun s => hstmt s labels₁ labels₂ hsub
    · intro ss
      induction ss with
      | nil => intros; trivial
      | cons s ss ih =>
        exact fun h => ⟨hstmt s _ _ hsub h.1, ih h.2⟩
  intro s
  induction s using Stmt.rec (motive_2 := fun ss =>
    ∀ labels₁ labels₂, (∀ l, l ∈ labels₁ → l ∈ labels₂) →
      Block.exitsCoveredByBlocks labels₁ ss →
      Block.exitsCoveredByBlocks labels₂ ss) with
  | cmd _ => intros; trivial
  | block l ss _ ih =>
    intro labels₁ labels₂ hsub h
    show Block.exitsCoveredByBlocks (l :: labels₂) ss
    exact ih (l :: labels₁) (l :: labels₂)
      (fun x hx => by cases hx with
        | head => exact .head _
        | tail _ hm => exact .tail _ (hsub x hm))
      h
  | ite _ tss ess _ ih_t ih_e =>
    intro labels₁ labels₂ hsub h
    exact ⟨ih_t labels₁ labels₂ hsub h.1, ih_e labels₁ labels₂ hsub h.2⟩
  | loop _ _ _ body _ ih =>
    intro labels₁ labels₂ hsub h
    exact ih labels₁ labels₂ hsub h
  | exit l _ =>
    intro labels₁ labels₂ hsub h
    exact hsub l h
  | funcDecl _ _ => intros; trivial
  | typeDecl _ _ => intros; trivial
  | nil => intros; trivial
  | cons s ss ih_s ih_ss =>
    rename_i labels₁ labels₂ hsub h
    exact ⟨ih_s labels₁ labels₂ hsub h.1, ih_ss labels₁ labels₂ hsub h.2⟩

/-- If every statement in a list is a `.cmd`, then `exitsCoveredByBlocks` holds
    for any labels (since `.cmd` has no exit statements). -/
theorem all_cmd_exitsCoveredByBlocks
    {P : PureExpr} {CmdT : Type}
    (labels : List String) (ss : List (Stmt P CmdT))
    (h : ∀ s ∈ ss, ∃ c, s = Stmt.cmd c) :
    Block.exitsCoveredByBlocks labels ss := by
  induction ss with
  | nil => trivial
  | cons hd tl ih =>
    constructor
    · obtain ⟨c, hc⟩ := h hd (.head _)
      subst hc; exact True.intro
    · exact ih (fun s hs => h s (.tail _ hs))

theorem Block.getBlockLabels_block_cons {P : PureExpr} {C : Type}
    (l : String) (bss : List (Stmt P C)) (md : MetaData P)
    (rest : List (Stmt P C)) :
    Block.getBlockLabels (.block l bss md :: rest) =
      (l :: Block.getBlockLabels bss) ++ Block.getBlockLabels rest := by
  show Block.getBlockLabels.stmtGetBlockLabels _ ++ _ = _
  rfl

theorem Block.getBlockLabels_ite_cons {P : PureExpr} {C : Type}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P C))
    (md : MetaData P) (rest : List (Stmt P C)) :
    Block.getBlockLabels (.ite c tss ess md :: rest) =
      (Block.getBlockLabels tss ++ Block.getBlockLabels ess)
        ++ Block.getBlockLabels rest := by
  show Block.getBlockLabels.stmtGetBlockLabels _ ++ _ = _
  rfl

theorem Block.getBlockLabels_loop_cons {P : PureExpr} {C : Type}
    (c : Imperative.ExprOrNondet P) (m : Option P.Expr)
    (is : List (String × P.Expr)) (bss : List (Stmt P C))
    (md : MetaData P) (rest : List (Stmt P C)) :
    Block.getBlockLabels (.loop c m is bss md :: rest) =
      Block.getBlockLabels bss ++ Block.getBlockLabels rest := by
  show Block.getBlockLabels.stmtGetBlockLabels _ ++ _ = _
  rfl

theorem Block.getBlockLabels_cmd_cons {P : PureExpr} {C : Type}
    (c : C) (rest : List (Stmt P C)) :
    Block.getBlockLabels (.cmd c :: rest) = Block.getBlockLabels rest := by
  show Block.getBlockLabels.stmtGetBlockLabels _ ++ _ = _
  rfl

theorem Block.getBlockLabels_funcDecl_cons {P : PureExpr} {C : Type}
    (decl : Imperative.PureFunc P) (md : MetaData P)
    (rest : List (Stmt P C)) :
    Block.getBlockLabels (.funcDecl decl md :: rest) =
      Block.getBlockLabels rest := by
  show Block.getBlockLabels.stmtGetBlockLabels _ ++ _ = _
  rfl

theorem Block.getBlockLabels_typeDecl_cons {P : PureExpr} {C : Type}
    (tc : TypeConstructor) (md : MetaData P)
    (rest : List (Stmt P C)) :
    Block.getBlockLabels (.typeDecl tc md :: rest) =
      Block.getBlockLabels rest := by
  show Block.getBlockLabels.stmtGetBlockLabels _ ++ _ = _
  rfl

theorem Block.getBlockLabels_exit_cons {P : PureExpr} {C : Type}
    (l : String) (md : MetaData P) (rest : List (Stmt P C)) :
    Block.getBlockLabels (.exit l md :: rest) =
      Block.getBlockLabels rest := by
  show Block.getBlockLabels.stmtGetBlockLabels _ ++ _ = _
  rfl

@[expose] def Block.userLabelsShapeNodup {P : PureExpr} {C : Type}
    (ss : List (Stmt P C)) : Prop :=
  (∀ l ∈ Block.getBlockLabels ss, ¬ String.HasUnderscoreDigitSuffix l) ∧
  (Block.getBlockLabels ss).Nodup

/-! # `getBlockLabels` is preserved by `nondetElim`

The structured-to-structured pass `Block.nondetElim` (eliminates
nondeterministic control) preserves the multiset *and order* of user-provided
`.block` labels: every label is carried through verbatim, and the only freshly
generated statements are `.cmd`s (which `getBlockLabels` ignores). Hence the
source-side well-formedness condition `userLabelsShapeNodup ss` (a function of
`getBlockLabels ss`) survives the pass. -/

/-! ## Distributivity helpers for `getBlockLabels`

`getBlockLabels` is a list-valued structural walk, so the per-constructor
`_out`/havoc-prefix lemmas of the pass (which split via `++` and
`List.map Stmt.cmd`) need these two distributivity facts. -/

/-- `getBlockLabels` of the empty block is empty. -/
theorem Block.getBlockLabels_nil {P : PureExpr} {C : Type} :
    Block.getBlockLabels ([] : List (Stmt P C)) = [] := rfl

/-- `getBlockLabels` distributes over list concatenation. -/
theorem Block.getBlockLabels_append {P : PureExpr} {C : Type}
    (ss₁ ss₂ : List (Stmt P C)) :
    Block.getBlockLabels (ss₁ ++ ss₂) =
      Block.getBlockLabels ss₁ ++ Block.getBlockLabels ss₂ := by
  induction ss₁ with
  | nil => simp [Block.getBlockLabels]
  | cons s rest ih =>
      simp only [List.cons_append, Block.getBlockLabels, ih, List.append_assoc]

/-- A list of `.cmd` statements contributes no user block labels. -/
theorem Block.getBlockLabels_map_cmd {P : PureExpr} {C : Type}
    (cs : List C) :
    Block.getBlockLabels (cs.map (@Stmt.cmd P C)) = ([] : List String) := by
  induction cs with
  | nil => simp [Block.getBlockLabels]
  | cons c rest ih =>
      simp only [List.map_cons]
      rw [Block.getBlockLabels_cmd_cons, ih]

/-! ### Distribution of Block-level shape predicates over `++`

These syntactic lemmas distribute the structural walkers (`initVars`,
`simpleShape`, `loopHasNoInvariants`, `modifiedVars`, `noInitsAnywhere`,
`loopBodyNoInits`) over list concatenation. They are consumed by the
transform correctness proofs, which all import this base module. -/

/-- Concatenation distributes over `Block.initVars`. -/
theorem Block.initVars_append (xs ys : List (Stmt P (Cmd P))) :
    Block.initVars (xs ++ ys) = Block.initVars xs ++ Block.initVars ys := by
  induction xs with
  | nil => simp [Block.initVars]
  | cons x rest ih =>
    simp [ih, List.append_assoc]

/-- `Block.simpleShape` distributes over `++`. -/
theorem Block.simpleShape_append (xs ys : List (Stmt P (Cmd P))) :
    Block.simpleShape (xs ++ ys) =
      (Block.simpleShape xs && Block.simpleShape ys) := by
  induction xs with
  | nil => simp [Block.simpleShape]
  | cons x rest ih => simp [Block.simpleShape, ih, Bool.and_assoc]

/-- `Block.loopHasNoInvariants` distributes over `++`. -/
theorem Block.loopHasNoInvariants_append (xs ys : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (xs ++ ys) =
      (Block.loopHasNoInvariants xs && Block.loopHasNoInvariants ys) := by
  induction xs with
  | nil => simp [Block.loopHasNoInvariants]
  | cons x rest ih => simp [Block.loopHasNoInvariants, ih, Bool.and_assoc]

/-- `Block.modifiedVars` distributes over list append. -/
theorem Block.modifiedVars_append (xs ys : List (Stmt P (Cmd P))) :
    Block.modifiedVars (xs ++ ys) = Block.modifiedVars xs ++ Block.modifiedVars ys := by
  induction xs with
  | nil => simp [Block.modifiedVars]
  | cons x rest ih =>
      simp only [List.cons_append, Block.modifiedVars, ih, List.append_assoc]

/-- Concatenation distributes over `Block.noInitsAnywhere`. -/
theorem Block.noInitsAnywhere_append (xs ys : List (Stmt P (Cmd P))) :
    Block.noInitsAnywhere (xs ++ ys) =
      (Block.noInitsAnywhere xs && Block.noInitsAnywhere ys) := by
  induction xs with
  | nil => simp [Block.noInitsAnywhere]
  | cons x rest ih =>
    simp [Block.noInitsAnywhere, ih, Bool.and_assoc]

/-- Concatenation distributes over `Block.loopBodyNoInits`. -/
theorem Block.loopBodyNoInits_append (xs ys : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (xs ++ ys) =
      (Block.loopBodyNoInits xs && Block.loopBodyNoInits ys) := by
  induction xs with
  | nil => simp [Block.loopBodyNoInits]
  | cons x rest ih =>
    simp [Block.loopBodyNoInits, ih, Bool.and_assoc]

/-- Concatenation distributes over `Block.noMeasureLoops`. -/
theorem Block.noMeasureLoops_append (xs ys : List (Stmt P (Cmd P))) :
    Block.noMeasureLoops (xs ++ ys) =
      (Block.noMeasureLoops xs && Block.noMeasureLoops ys) := by
  induction xs with
  | nil => simp [Block.noMeasureLoops]
  | cons x rest ih => simp [Block.noMeasureLoops, ih, Bool.and_assoc]

/-- Concatenation distributes over `Block.noFuncDecl`. -/
theorem Block.noFuncDecl_append (xs ys : List (Stmt P (Cmd P))) :
    Block.noFuncDecl (xs ++ ys) =
      (Block.noFuncDecl xs && Block.noFuncDecl ys) := by
  induction xs with
  | nil => simp [Block.noFuncDecl]
  | cons x rest ih => simp [Block.noFuncDecl, ih, Bool.and_assoc]

mutual
/-- Under `noFuncDecl`, a statement's defined variables coincide with its
init variables (no `funcDecl` means no scoped-only definitions). -/
theorem Stmt.definedVars_eq_initVars_of_noFuncDecl [HasIdent P] [HasVarsPure P P.Expr]
    (s : Stmt P (Cmd P)) (h : Stmt.noFuncDecl s = true) :
    Stmt.definedVars (P := P) (C := Cmd P) s false = Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp only [Stmt.definedVars, Stmt.initVars, Cmd.definedVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      rw [Stmt.definedVars, Stmt.initVars_block, Stmt.noFuncDecl] at *
      simp only [Bool.false_eq_true, if_false]
      exact Block.definedVars_eq_initVars_of_noFuncDecl bss h
  | .ite g tss ess md =>
      rw [Stmt.definedVars, Stmt.initVars_ite, Stmt.noFuncDecl, Bool.and_eq_true] at *
      simp only [Bool.false_eq_true, if_false]
      rw [Block.definedVars_eq_initVars_of_noFuncDecl tss h.1,
          Block.definedVars_eq_initVars_of_noFuncDecl ess h.2]
  | .loop g m inv body md =>
      rw [Stmt.definedVars, Stmt.initVars_loop, Stmt.noFuncDecl] at *
      simp only [Bool.false_eq_true, if_false]
      exact Block.definedVars_eq_initVars_of_noFuncDecl body h
  | .exit lbl md => simp [Stmt.definedVars, Stmt.initVars]
  | .funcDecl d md => rw [Stmt.noFuncDecl] at h; exact absurd h (by simp)
  | .typeDecl t md => simp [Stmt.definedVars, Stmt.initVars]
  termination_by sizeOf s

theorem Block.definedVars_eq_initVars_of_noFuncDecl [HasIdent P] [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P))) (h : Block.noFuncDecl ss = true) :
    Block.definedVars (P := P) (C := Cmd P) ss false = Block.initVars ss := by
  match ss with
  | [] => simp [Block.definedVars, Block.initVars]
  | s :: rest =>
      rw [Block.definedVars, Block.initVars_cons, Block.noFuncDecl, Bool.and_eq_true] at *
      rw [Stmt.definedVars_eq_initVars_of_noFuncDecl s h.1,
          Block.definedVars_eq_initVars_of_noFuncDecl rest h.2]
  termination_by sizeOf ss
end

/-- If `y ∉ Block.definedVars ss`, then `y ∉ Stmt.definedVars s` for `s ∈ ss`. -/
theorem all_not_mem_definedVars_of_block [HasIdent P] [HasVarsPure P P.Expr]
    {y : P.Ident} {ss : List (Stmt P (Cmd P))}
    (h : y ∉ Block.definedVars (P := P) (C := Cmd P) ss false) :
    ∀ s ∈ ss, y ∉ Stmt.definedVars (P := P) (C := Cmd P) s false := by
  induction ss with
  | nil => intro s hs; exact absurd hs (List.not_mem_nil)
  | cons s rest ih =>
    rw [Block.definedVars] at h
    intro s' hs'
    rcases List.mem_cons.mp hs' with h_eq | h_in
    · exact h_eq ▸ (fun hc => h (List.mem_append.mpr (Or.inl hc)))
    · exact ih (fun hc => h (List.mem_append.mpr (Or.inr hc))) s' h_in

mutual
/-- Every init variable of a statement is one of its defined variables. -/
theorem Stmt.mem_initVars_mem_definedVars {P : PureExpr} [HasIdent P] [HasVarsPure P P.Expr]
    {y : P.Ident} {s : Stmt P (Cmd P)} (hy : y ∈ Stmt.initVars s) :
    y ∈ Stmt.definedVars (P := P) (C := Cmd P) s false := by
  match s with
  | .cmd c =>
    cases c <;>
      simp_all only [Stmt.initVars, Stmt.definedVars, Cmd.definedVars,
        HasVarsImp.definedVars, List.not_mem_nil, List.mem_singleton]
  | .block lbl bss md =>
    rw [Stmt.initVars_block] at hy
    rw [Stmt.definedVars]; simp only [Bool.false_eq_true, if_false]
    exact Block.mem_initVars_mem_definedVars hy
  | .ite g tss ess md =>
    rw [Stmt.initVars_ite] at hy
    rw [Stmt.definedVars]; simp only [Bool.false_eq_true, if_false]
    rcases List.mem_append.mp hy with h | h
    · exact List.mem_append_left _ (Block.mem_initVars_mem_definedVars h)
    · exact List.mem_append_right _ (Block.mem_initVars_mem_definedVars h)
  | .loop g m inv body md =>
    rw [Stmt.initVars_loop] at hy
    rw [Stmt.definedVars]; simp only [Bool.false_eq_true, if_false]
    exact Block.mem_initVars_mem_definedVars hy
  | .exit lbl md => simp only [Stmt.initVars] at hy; exact absurd hy (by simp)
  | .funcDecl d md => simp only [Stmt.initVars] at hy; exact absurd hy (by simp)
  | .typeDecl t md => simp only [Stmt.initVars] at hy; exact absurd hy (by simp)
  termination_by sizeOf s

theorem Block.mem_initVars_mem_definedVars {P : PureExpr} [HasIdent P] [HasVarsPure P P.Expr]
    {y : P.Ident} {ss : List (Stmt P (Cmd P))} (hy : y ∈ Block.initVars ss) :
    y ∈ Block.definedVars (P := P) (C := Cmd P) ss false := by
  match ss with
  | [] => simp only [Block.initVars] at hy; exact absurd hy (by simp)
  | s :: rest =>
    rw [Block.initVars_cons] at hy
    rw [Block.definedVars]
    rcases List.mem_append.mp hy with h | h
    · exact List.mem_append_left _ (Stmt.mem_initVars_mem_definedVars h)
    · exact List.mem_append_right _ (Block.mem_initVars_mem_definedVars h)
  termination_by sizeOf ss
end

mutual
/-- A simple-shape statement contains no nondeterministic loop. -/
theorem Stmt.not_containsNondetLoop_of_simpleShape {P : PureExpr}
    (s : Stmt P (Cmd P)) (h : Stmt.simpleShape s = true) :
    Stmt.containsNondetLoop s = false := by
  match s with
  | .cmd c => rw [Stmt.containsNondetLoop]
  | .block lbl bss md =>
      rw [Stmt.containsNondetLoop]
      rw [Stmt.simpleShape] at h
      exact Block.not_containsNondetLoop_of_simpleShape bss h
  | .ite (.det e) tss ess md =>
      rw [Stmt.containsNondetLoop, Bool.or_eq_false_iff]
      rw [Stmt.simpleShape, Bool.and_eq_true] at h
      exact ⟨Block.not_containsNondetLoop_of_simpleShape tss h.1,
             Block.not_containsNondetLoop_of_simpleShape ess h.2⟩
  | .ite .nondet tss ess md => rw [Stmt.simpleShape] at h; exact absurd h (by simp)
  | .loop (.det e) m inv body md =>
      rw [Stmt.containsNondetLoop]
      rw [Stmt.simpleShape, Bool.and_eq_true] at h
      exact Block.not_containsNondetLoop_of_simpleShape body h.2
  | .loop .nondet m inv body md =>
      rw [Stmt.simpleShape] at h; exact absurd h (by simp)
  | .exit lbl md => rw [Stmt.containsNondetLoop]
  | .funcDecl d md => rw [Stmt.containsNondetLoop]
  | .typeDecl t md => rw [Stmt.containsNondetLoop]
  termination_by sizeOf s

/-- A simple-shape block contains no nondeterministic loop. -/
theorem Block.not_containsNondetLoop_of_simpleShape {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (h : Block.simpleShape ss = true) :
    Block.containsNondetLoop ss = false := by
  match ss with
  | [] => rw [Block.containsNondetLoop]
  | s :: rest =>
      rw [Block.containsNondetLoop, Bool.or_eq_false_iff]
      rw [Block.simpleShape, Bool.and_eq_true] at h
      exact ⟨Stmt.not_containsNondetLoop_of_simpleShape s h.1,
             Block.not_containsNondetLoop_of_simpleShape rest h.2⟩
  termination_by sizeOf ss
end

/-- Coverage of a singleton statement list reduces to coverage of the statement. -/
theorem coveredBlock_singleton {P : PureExpr} (labels : List String)
    (s : Stmt P (Cmd P)) (h : Stmt.exitsCoveredByBlocks labels s) :
    Block.exitsCoveredByBlocks labels [s] :=
  ⟨h, trivial⟩

theorem Cmds.definedVars_cons
    {P : PureExpr} (c : Cmd P) (cs : List (Cmd P)) :
    Cmds.definedVars (c :: cs) = Cmd.definedVars c ++ Cmds.definedVars cs := by
  rw [Cmds.definedVars.eq_def]

theorem Cmds.modifiedVars_cons
    {P : PureExpr} (c : Cmd P) (cs : List (Cmd P)) :
    Cmds.modifiedVars (c :: cs) = Cmd.modifiedVars c ++ Cmds.modifiedVars cs := by
  rw [Cmds.modifiedVars.eq_def]

/-! ## User-provided block-label disjointness

`userLabelsShapeNodup`/`userLabelsDisjoint` capture the well-formedness
condition on user-provided `.block` labels needed to produce a CFG with unique
block labels: labels are shape-free (no `_<digits>` generator suffix), pairwise
distinct, and disjoint from a generator state's output. -/

/-- A shape-free user label is never in `stringGens` of any WF state. -/
theorem userLabel_not_in_stringGens_of_shape_free
    {σ : StringGenState} (hwf : StringGenState.WF σ)
    {l : String} (h_shape : ¬ String.HasUnderscoreDigitSuffix l) :
    l ∉ StringGenState.stringGens σ :=
  StringGenState.not_mem_stringGens_of_not_hasUnderscoreDigitSuffix hwf h_shape

/-- A predicate stating that user-provided block labels:
1. are shape-free (do not have the `_<digits>` generator suffix), and
2. consequently do not collide with any label in any WF generator state, and
3. are pairwise distinct (no two `Stmt.block` constructors share a label).

This is the precondition needed for `stmtsToBlocks` to produce a CFG with
unique block labels. The shape-free clause is what cleanly distinguishes user
labels from generator output: client code chooses readable labels (e.g.
`"my_block"`) which never collide with `gen`'s `pf_42`-style output. -/
@[expose] def Block.userLabelsDisjoint {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (gen' : StringGenState) : Prop :=
  (∀ l ∈ Block.getBlockLabels ss, ¬ String.HasUnderscoreDigitSuffix l) ∧
  (Block.getBlockLabels ss).Nodup ∧
  (∀ l ∈ Block.getBlockLabels ss, l ∉ StringGenState.stringGens gen')

/-- `userLabelsShapeNodup` recovers `userLabelsDisjoint` at any WF generator
state: the third (disjointness) conjunct follows from the shape-free conjunct via
`userLabel_not_in_stringGens_of_shape_free`. -/
theorem Block.userLabelsDisjoint_of_shapeNodup {P : PureExpr}
    (ss : List (Stmt P (Cmd P)))
    (h : Block.userLabelsShapeNodup ss) :
    ∀ gen : StringGenState, StringGenState.WF gen →
      Block.userLabelsDisjoint ss gen := by
  intro gen hwf
  refine ⟨h.1, h.2, ?_⟩
  intro l hl
  exact userLabel_not_in_stringGens_of_shape_free hwf (h.1 l hl)

/-- `userLabelsDisjoint` distributes over `cons`: if a longer list is
disjoint, so is the tail. -/
theorem Block.userLabelsDisjoint_tail {P : PureExpr}
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (s :: rest) gen') :
    Block.userLabelsDisjoint rest gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro l hl; apply h_shape; unfold Block.getBlockLabels
    exact List.mem_append.mpr (Or.inr hl)
  · unfold Block.getBlockLabels at h_nodup
    exact (List.nodup_append.mp h_nodup).2.1
  · intro l hl; apply h_disj; unfold Block.getBlockLabels
    exact List.mem_append.mpr (Or.inr hl)

/-- `userLabelsDisjoint` is antitone in the generator state: a smaller
generator state can only have fewer labels, so disjointness is preserved
when restricting to a subset. -/
theorem Block.userLabelsDisjoint_mono {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (gen gen' : StringGenState)
    (h : Block.userLabelsDisjoint ss gen')
    (h_sub : StringGenState.stringGens gen ⊆ StringGenState.stringGens gen') :
    Block.userLabelsDisjoint ss gen := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨h_shape, h_nodup, ?_⟩
  intro l hl h_in_gen
  exact h_disj l hl (h_sub h_in_gen)

/-- `userLabelsDisjoint` for the body of a `Stmt.block`: if the outer
`Stmt.block l bss md :: rest` is disjoint, so are `bss`'s user labels. -/
theorem Block.userLabelsDisjoint_block_body {P : PureExpr}
    (l : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.block l bss md :: rest) gen') :
    Block.userLabelsDisjoint bss gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    apply h_shape
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr hx)))
  · -- bss's labels appear inside (l :: bss-labels) ++ rest-labels, so Nodup follows
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels at h_nodup
    have := (List.nodup_append.mp h_nodup).1
    exact (List.nodup_cons.mp this).2
  · intro x hx
    apply h_disj
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr hx)))

/-- `userLabelsDisjoint` for the then/else branches of a `Stmt.ite`. -/
theorem Block.userLabelsDisjoint_ite_then {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.ite c tss ess md :: rest) gen') :
    Block.userLabelsDisjoint tss gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; apply h_shape
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))
  · unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels at h_nodup
    have := (List.nodup_append.mp h_nodup).1
    exact (List.nodup_append.mp this).1
  · intro x hx; apply h_disj
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))

/-- `userLabelsDisjoint` for the then/else branches of a `Stmt.ite` (else side). -/
theorem Block.userLabelsDisjoint_ite_else {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.ite c tss ess md :: rest) gen') :
    Block.userLabelsDisjoint ess gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; apply h_shape
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))
  · unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels at h_nodup
    have := (List.nodup_append.mp h_nodup).1
    exact (List.nodup_append.mp this).2.1
  · intro x hx; apply h_disj
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))

/-- `userLabelsDisjoint` for the body of a `Stmt.loop`. -/
theorem Block.userLabelsDisjoint_loop_body {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (m : Option P.Expr) (is : List (String × P.Expr))
    (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.loop c m is bss md :: rest) gen') :
    Block.userLabelsDisjoint bss gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; apply h_shape
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl hx)
  · unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels at h_nodup
    exact (List.nodup_append.mp h_nodup).1
  · intro x hx; apply h_disj
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl hx)

/-- Cross-disjointness for `ite`: `tss`'s and `ess`'s user labels are
disjoint (lifted from the outer `Nodup`). -/
theorem Block.userLabels_ite_cross_disj {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.ite c tss ess md :: rest) gen') :
    (∀ x ∈ Block.getBlockLabels tss, x ∉ Block.getBlockLabels ess) ∧
    (∀ x ∈ Block.getBlockLabels tss, x ∉ Block.getBlockLabels rest) ∧
    (∀ x ∈ Block.getBlockLabels ess, x ∉ Block.getBlockLabels rest) := by
  obtain ⟨_, h_nodup, _⟩ := h
  rw [Block.getBlockLabels_ite_cons] at h_nodup
  -- h_nodup : ((tss-lbls ++ ess-lbls) ++ rest-lbls).Nodup
  have h_outer := List.nodup_append.mp h_nodup
  -- left = tss-lbls ++ ess-lbls; right = rest-lbls
  have h_te_nodup := h_outer.1
  have h_te_inner := List.nodup_append.mp h_te_nodup
  refine ⟨?_, ?_, ?_⟩
  · -- tss vs ess
    intro x h_t h_e
    exact h_te_inner.2.2 x h_t x h_e rfl
  · -- tss vs rest: x ∈ tss-lbls ⊆ left, x ∈ rest-lbls = right
    intro x h_t h_r
    exact h_outer.2.2 x (List.mem_append.mpr (Or.inl h_t)) x h_r rfl
  · -- ess vs rest
    intro x h_e h_r
    exact h_outer.2.2 x (List.mem_append.mpr (Or.inr h_e)) x h_r rfl

/-- Cross-disjointness for `loop`: `bss`'s user labels are disjoint from
`rest`'s user labels. -/
theorem Block.userLabels_loop_cross_disj {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (m : Option P.Expr) (is : List (String × P.Expr))
    (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.loop c m is bss md :: rest) gen') :
    ∀ x ∈ Block.getBlockLabels bss, x ∉ Block.getBlockLabels rest := by
  obtain ⟨_, h_nodup, _⟩ := h
  rw [Block.getBlockLabels_loop_cons] at h_nodup
  have h_outer := List.nodup_append.mp h_nodup
  intro x h_b h_r
  exact h_outer.2.2 x h_b x h_r rfl

/-- The label `l` of a `Stmt.block l bss md` is in the user-label list, so we
can lift the shape-free, Nodup, and disjointness facts to it. -/
theorem Block.userLabel_of_block_head {P : PureExpr}
    (l : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.block l bss md :: rest) gen') :
    ¬ String.HasUnderscoreDigitSuffix l ∧
    l ∉ StringGenState.stringGens gen' ∧
    l ∉ Block.getBlockLabels bss ∧
    l ∉ Block.getBlockLabels rest := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  have h_l_in : l ∈ Block.getBlockLabels (Stmt.block l bss md :: rest) := by
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))
  refine ⟨h_shape l h_l_in, h_disj l h_l_in, ?_, ?_⟩
  · -- l ∉ Block.getBlockLabels bss: from Nodup of (l :: bss-labels) ++ rest-labels
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels at h_nodup
    have h_left := (List.nodup_append.mp h_nodup).1
    exact (List.nodup_cons.mp h_left).1
  · -- l ∉ Block.getBlockLabels rest: from cross-list disjointness in Nodup append
    unfold Block.getBlockLabels Block.getBlockLabels.stmtGetBlockLabels at h_nodup
    have h_disj_lr := (List.nodup_append.mp h_nodup).2.2
    intro h_in
    exact h_disj_lr l (List.mem_cons.mpr (Or.inl rfl)) l h_in rfl

/-! ## Block.uniqueInits projection helpers

`Block.uniqueInits ss` is a Nodup property of the cumulative `Block.initVars ss`
list. These mechanical helpers project Nodup down to sub-lists that recursive
simulation calls produce. -/

theorem Block.uniqueInits.tail {P : PureExpr}
    {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (s :: ss)) : Block.uniqueInits ss := by
  unfold Block.uniqueInits at h ⊢
  rw [Block.initVars] at h
  exact (List.nodup_append.mp h).2.1

theorem Block.uniqueInits.head_stmt {P : PureExpr}
    {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (s :: ss)) : (Stmt.initVars s).Nodup := by
  unfold Block.uniqueInits at h
  rw [Block.initVars] at h
  exact (List.nodup_append.mp h).1

theorem Block.uniqueInits.block_body {P : PureExpr}
    {label : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (.block label bss md :: rest)) :
    Block.uniqueInits bss := by
  have h_head := Block.uniqueInits.head_stmt h
  -- Stmt.initVars (.block ...) = Block.initVars bss; so Nodup carries over.
  unfold Stmt.initVars at h_head
  exact h_head

theorem Block.uniqueInits.ite_then {P : PureExpr}
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (.ite g tss ess md :: rest)) :
    Block.uniqueInits tss := by
  have h_head := Block.uniqueInits.head_stmt h
  -- Stmt.initVars (.ite _ tss ess _) = Block.initVars tss ++ Block.initVars ess
  unfold Stmt.initVars at h_head
  exact (List.nodup_append.mp h_head).1

theorem Block.uniqueInits.ite_else {P : PureExpr}
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (.ite g tss ess md :: rest)) :
    Block.uniqueInits ess := by
  have h_head := Block.uniqueInits.head_stmt h
  unfold Stmt.initVars at h_head
  exact (List.nodup_append.mp h_head).2.1

/-! ## `loopBodyNoInits` peel helpers. -/

theorem initfree_cons {P : PureExpr}
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))}
    (h : Block.loopBodyNoInits (s :: rest) = true) :
    Stmt.loopBodyNoInits s = true ∧ Block.loopBodyNoInits rest = true := by
  simp only [Block.loopBodyNoInits, Bool.and_eq_true] at h
  exact h

theorem initfree_block {P : PureExpr}
    {lbl : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : Stmt.loopBodyNoInits (.block lbl bss md) = true) :
    Block.loopBodyNoInits bss = true := by
  simpa [Stmt.loopBodyNoInits] using h

theorem initfree_ite {P : PureExpr}
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : Stmt.loopBodyNoInits (.ite g tss ess md) = true) :
    Block.loopBodyNoInits tss = true ∧ Block.loopBodyNoInits ess = true := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true] at h
  exact h

/-! ## `Cmds.definedVars` distributes over `++`. -/

theorem Cmds.definedVars_append {P : PureExpr} (xs ys : List (Cmd P)) :
    Cmds.definedVars (xs ++ ys) = Cmds.definedVars xs ++ Cmds.definedVars ys := by
  induction xs with
  | nil => simp [Cmds.definedVars]
  | cons c rest ih => simp only [List.cons_append, Cmds.definedVars, ih, List.append_assoc]

/-! ## `transportShape` distributes over `++`. -/

theorem Block.transportShape_append {P : PureExpr} (xs ys : List (Stmt P (Cmd P))) :
    Block.transportShape (xs ++ ys) = (Block.transportShape xs && Block.transportShape ys) := by
  induction xs with
  | nil => simp [Block.transportShape]
  | cons x rest ih => simp only [List.cons_append, Block.transportShape, ih, Bool.and_assoc]

/-! ## An init-free, funcDecl-free (block of) statement(s) defines no variables. -/

mutual
/-- An init-free, funcDecl-free statement defines no variables. -/
theorem stmt_definedVars_nil_of_noInits_noFuncDecl {P : PureExpr} (s : Stmt P (Cmd P))
    (h_ni : Stmt.noInitsAnywhere s = true) (h_nf : Stmt.noFuncDecl s = true) :
    Stmt.definedVars s false = [] := by
  match s with
  | .cmd (.init _ _ _ _) => exact absurd h_ni (by simp [Stmt.noInitsAnywhere])
  | .cmd (.set _ _ _) => with_unfolding_all rfl
  | .cmd (.assert _ _ _) => with_unfolding_all rfl
  | .cmd (.assume _ _ _) => with_unfolding_all rfl
  | .cmd (.cover _ _ _) => with_unfolding_all rfl
  | .block lbl bss md =>
      rw [Stmt.definedVars]; show Block.definedVars bss false = []
      exact block_definedVars_nil_of_noInits_noFuncDecl bss
        (by simpa [Stmt.noInitsAnywhere] using h_ni) (by simpa [Stmt.noFuncDecl] using h_nf)
  | .ite g tss ess md =>
      rw [Stmt.definedVars]; show Block.definedVars tss false ++ Block.definedVars ess false = []
      simp only [Stmt.noInitsAnywhere, Bool.and_eq_true] at h_ni
      simp only [Stmt.noFuncDecl, Bool.and_eq_true] at h_nf
      rw [block_definedVars_nil_of_noInits_noFuncDecl tss h_ni.1 h_nf.1,
          block_definedVars_nil_of_noInits_noFuncDecl ess h_ni.2 h_nf.2]; rfl
  | .loop g m inv body md =>
      rw [Stmt.definedVars]; show Block.definedVars body false = []
      exact block_definedVars_nil_of_noInits_noFuncDecl body
        (by simpa [Stmt.noInitsAnywhere] using h_ni) (by simpa [Stmt.noFuncDecl] using h_nf)
  | .exit lbl md => simp [Stmt.definedVars]
  | .funcDecl d md => exact absurd h_nf (by simp [Stmt.noFuncDecl])
  | .typeDecl t md => simp [Stmt.definedVars]
  termination_by sizeOf s

theorem block_definedVars_nil_of_noInits_noFuncDecl {P : PureExpr} (body : List (Stmt P (Cmd P)))
    (h_ni : Block.noInitsAnywhere body = true) (h_nf : Block.noFuncDecl body = true) :
    Block.definedVars body false = [] := by
  match body with
  | [] => with_unfolding_all rfl
  | s :: rest =>
      rw [Block.definedVars]; show Stmt.definedVars s false ++ Block.definedVars rest false = []
      simp only [Block.noInitsAnywhere, Bool.and_eq_true] at h_ni
      simp only [Block.noFuncDecl, Bool.and_eq_true] at h_nf
      rw [stmt_definedVars_nil_of_noInits_noFuncDecl s h_ni.1 h_nf.1,
          block_definedVars_nil_of_noInits_noFuncDecl rest h_ni.2 h_nf.2]; rfl
  termination_by sizeOf body
end

/-! ## `transportShape` from the `.loop` arm Bool preconditions.

`transportShape` FOLLOWS FROM the genuine `.loop` arm Bool preconditions ALONE
(`containsNondetLoop = false`, `noFuncDecl = true`, `loopHasNoInvariants =
true`, `noMeasureLoops = true`).  Proved by mutual structural induction; each
statement constructor reduces to its sub-blocks under the corresponding Bool-walker
reductions. -/
mutual
theorem Stmt.transportShape_of_arm_preconds {P : PureExpr}
    (s : Stmt P (Cmd P))
    (h_nd : Stmt.containsNondetLoop s = false)
    (h_fd : Stmt.noFuncDecl s = true)
    (h_inv : Stmt.loopHasNoInvariants s = true)
    (h_measure : Stmt.noMeasureLoops s = true) :
    Stmt.transportShape s = true := by
  match s with
  | .cmd c =>
      cases c with
      | init _ _ rhs _ => cases rhs <;> simp only [Stmt.transportShape]
      | set _ rhs _ => cases rhs <;> simp only [Stmt.transportShape]
      | assert _ _ _ => simp only [Stmt.transportShape]
      | assume _ _ _ => simp only [Stmt.transportShape]
      | cover _ _ _ => simp only [Stmt.transportShape]
  | .block lbl bss md =>
      simp only [Stmt.transportShape]
      exact Block.transportShape_of_arm_preconds bss
        (by simpa only [Stmt.containsNondetLoop] using h_nd)
        (by simpa only [Stmt.noFuncDecl] using h_fd)
        (by simpa only [Stmt.loopHasNoInvariants] using h_inv)
        (by simpa only [Stmt.noMeasureLoops] using h_measure)
  | .ite g tss ess md =>
      simp only [Stmt.containsNondetLoop, Bool.or_eq_false_iff] at h_nd
      simp only [Stmt.noFuncDecl, Bool.and_eq_true] at h_fd
      simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h_inv
      simp only [Stmt.noMeasureLoops, Bool.and_eq_true] at h_measure
      have h_t := Block.transportShape_of_arm_preconds tss h_nd.1 h_fd.1 h_inv.1 h_measure.1
      have h_e := Block.transportShape_of_arm_preconds ess h_nd.2 h_fd.2 h_inv.2 h_measure.2
      cases g <;>
        simp only [Stmt.transportShape, Bool.and_eq_true] <;> exact ⟨h_t, h_e⟩
  | .loop g m inv body md =>
      cases g with
      | nondet => exact absurd h_nd (by simp [Stmt.containsNondetLoop])
      | det g' =>
        have h_m : m = none := by
          rw [Stmt.noMeasureLoops, Bool.and_eq_true] at h_measure
          exact Option.isNone_iff_eq_none.mp h_measure.1
        have h_inv_nil : inv = [] := by
          rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h_inv
          exact List.isEmpty_iff.mp h_inv.1
        subst h_m; subst h_inv_nil
        simp only [Stmt.transportShape]
        exact Block.transportShape_of_arm_preconds body
          (by simpa only [Stmt.containsNondetLoop] using h_nd)
          (by simpa only [Stmt.noFuncDecl] using h_fd)
          (by rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h_inv; exact h_inv.2)
          (by rw [Stmt.noMeasureLoops, Bool.and_eq_true] at h_measure; exact h_measure.2)
  | .exit lbl md => simp only [Stmt.transportShape]
  | .funcDecl d md => exact absurd h_fd (by simp [Stmt.noFuncDecl])
  | .typeDecl t md => simp only [Stmt.transportShape]
  termination_by sizeOf s

theorem Block.transportShape_of_arm_preconds {P : PureExpr}
    (ss : List (Stmt P (Cmd P)))
    (h_nd : Block.containsNondetLoop ss = false)
    (h_fd : Block.noFuncDecl ss = true)
    (h_inv : Block.loopHasNoInvariants ss = true)
    (h_measure : Block.noMeasureLoops ss = true) :
    Block.transportShape ss = true := by
  match ss with
  | [] => simp only [Block.transportShape]
  | s :: rest =>
      simp only [Block.containsNondetLoop, Bool.or_eq_false_iff] at h_nd
      simp only [Block.noFuncDecl, Bool.and_eq_true] at h_fd
      simp only [Block.loopHasNoInvariants, Bool.and_eq_true] at h_inv
      simp only [Block.noMeasureLoops, Bool.and_eq_true] at h_measure
      simp only [Block.transportShape, Bool.and_eq_true]
      exact ⟨Stmt.transportShape_of_arm_preconds s h_nd.1 h_fd.1 h_inv.1 h_measure.1,
             Block.transportShape_of_arm_preconds rest h_nd.2 h_fd.2 h_inv.2 h_measure.2⟩
  termination_by sizeOf ss
end

/-! ## Freshness / shape-freedom predicate property lemmas

Property lemmas over the `namesFreshInExprs`, `namesFreshInRhsExprs`, and
`exprsShapeFree` predicate families (defined in `Strata.DL.Imperative.Stmt`).
Each leaf freshness condition is a `List.Disjoint`, so many lemmas reduce to the
`List.Disjoint` API. -/

mutual

/-- The full `namesFreshInExprs` implies the RHS-only relaxation: the RHS-only
predicate checks a subset of `getVars`'s positions, and `namesFreshInExprs` is
disjointness from all of `getVars`. -/
theorem Stmt.namesFreshInRhsExprs_of_namesFreshInExprs {P : PureExpr} [HasFvars P]
    (names : List P.Ident) (s : Stmt P (Cmd P))
    (h : Stmt.namesFreshInExprs names s) :
    Stmt.namesFreshInRhsExprs names s := by
  match s with
  | .cmd (.init _ _ rhs _) => simpa only [Stmt.namesFreshInRhsExprs] using
      (by simpa only [Stmt.namesFreshInExprs, Stmt.getVars, HasVarsPure.getVars, Cmd.getVars] using h)
  | .cmd (.set _ rhs _) => simpa only [Stmt.namesFreshInRhsExprs] using
      (by simpa only [Stmt.namesFreshInExprs, Stmt.getVars, HasVarsPure.getVars, Cmd.getVars] using h)
  | .cmd (.assert _ e _) => simpa only [Stmt.namesFreshInRhsExprs] using
      (by simpa only [Stmt.namesFreshInExprs, Stmt.getVars, HasVarsPure.getVars, Cmd.getVars] using h)
  | .cmd (.assume _ e _) => simpa only [Stmt.namesFreshInRhsExprs] using
      (by simpa only [Stmt.namesFreshInExprs, Stmt.getVars, HasVarsPure.getVars, Cmd.getVars] using h)
  | .cmd (.cover _ e _) => simpa only [Stmt.namesFreshInRhsExprs] using
      (by simpa only [Stmt.namesFreshInExprs, Stmt.getVars, HasVarsPure.getVars, Cmd.getVars] using h)
  | .block _ bss _ =>
      simp only [Stmt.namesFreshInExprs, Stmt.getVars] at h
      simp only [Stmt.namesFreshInRhsExprs]
      exact Block.namesFreshInRhsExprs_of_namesFreshInExprs names bss h
  | .ite g tss ess _ =>
      simp only [Stmt.namesFreshInExprs, Stmt.getVars] at h
      simp only [Stmt.namesFreshInRhsExprs]
      refine ⟨Block.namesFreshInRhsExprs_of_namesFreshInExprs names tss ?_,
              Block.namesFreshInRhsExprs_of_namesFreshInExprs names ess ?_⟩
      · exact fun a ha hmem => h ha (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hmem))))
      · exact fun a ha hmem => h ha (List.mem_append.mpr (Or.inr hmem))
  | .loop g m inv body _ =>
      simp only [Stmt.namesFreshInExprs, Stmt.getVars] at h
      simp only [Stmt.namesFreshInRhsExprs]
      exact Block.namesFreshInRhsExprs_of_namesFreshInExprs names body
        (fun a ha hmem => h ha (List.mem_append.mpr (Or.inr hmem)))
  | .exit _ _ => simp only [Stmt.namesFreshInRhsExprs]
  | .funcDecl _ _ => simp only [Stmt.namesFreshInRhsExprs]
  | .typeDecl _ _ => simp only [Stmt.namesFreshInRhsExprs]
  termination_by sizeOf s

theorem Block.namesFreshInRhsExprs_of_namesFreshInExprs {P : PureExpr} [HasFvars P]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P)))
    (h : Block.namesFreshInExprs names ss) :
    Block.namesFreshInRhsExprs names ss := by
  match ss with
  | [] => simp only [Block.namesFreshInRhsExprs]
  | s :: rest =>
      simp only [Block.namesFreshInExprs, Block.getVars] at h
      simp only [Block.namesFreshInRhsExprs]
      exact ⟨Stmt.namesFreshInRhsExprs_of_namesFreshInExprs names s
               (fun a ha hmem => h ha (List.mem_append.mpr (Or.inl hmem))),
             Block.namesFreshInRhsExprs_of_namesFreshInExprs names rest
               (fun a ha hmem => h ha (List.mem_append.mpr (Or.inr hmem)))⟩
  termination_by sizeOf ss

end

mutual
/-- `namesFreshInRhsExprs` is monotone in the `names` subset relation: a
smaller name list is a weaker requirement. -/
theorem Stmt.namesFreshInRhsExprs_subset {P : PureExpr}
    [HasFvars P] {names₁ names₂ : List P.Ident}
    (h_sub : names₁ ⊆ names₂)
    (s : Stmt P (Cmd P))
    (h : Stmt.namesFreshInRhsExprs names₂ s) :
    Stmt.namesFreshInRhsExprs names₁ s := by
  cases s with
  | cmd c =>
    cases c <;>
      · simp only [Stmt.namesFreshInRhsExprs] at h ⊢
        exact List.Disjoint_Subset_left h h_sub
  | block lbl bss md =>
    simp only [Stmt.namesFreshInRhsExprs] at h ⊢
    exact Block.namesFreshInRhsExprs_subset h_sub bss h
  | ite g tss ess md =>
    simp only [Stmt.namesFreshInRhsExprs] at h ⊢
    exact ⟨Block.namesFreshInRhsExprs_subset h_sub tss h.1,
           Block.namesFreshInRhsExprs_subset h_sub ess h.2⟩
  | loop g m inv body md =>
    simp only [Stmt.namesFreshInRhsExprs] at h ⊢
    exact Block.namesFreshInRhsExprs_subset h_sub body h
  | exit lbl md => simp only [Stmt.namesFreshInRhsExprs]
  | funcDecl d md => simp only [Stmt.namesFreshInRhsExprs]
  | typeDecl t md => simp only [Stmt.namesFreshInRhsExprs]
  termination_by sizeOf s

theorem Block.namesFreshInRhsExprs_subset {P : PureExpr}
    [HasFvars P] {names₁ names₂ : List P.Ident}
    (h_sub : names₁ ⊆ names₂)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.namesFreshInRhsExprs names₂ ss) :
    Block.namesFreshInRhsExprs names₁ ss := by
  match ss with
  | [] => simp only [Block.namesFreshInRhsExprs]
  | s :: rest =>
    simp only [Block.namesFreshInRhsExprs] at h ⊢
    exact ⟨Stmt.namesFreshInRhsExprs_subset h_sub s h.1,
           Block.namesFreshInRhsExprs_subset h_sub rest h.2⟩
  termination_by sizeOf ss
end

/-- `Block.namesFreshInRhsExprs` distributes over `++`. -/
theorem Block.namesFreshInRhsExprs_append {P : PureExpr}
    [HasFvars P] {names : List P.Ident}
    (xs ys : List (Stmt P (Cmd P)))
    (hx : Block.namesFreshInRhsExprs names xs)
    (hy : Block.namesFreshInRhsExprs names ys) :
    Block.namesFreshInRhsExprs names (xs ++ ys) := by
  induction xs with
  | nil => simpa only [List.nil_append] using hy
  | cons x rest ih =>
    simp only [Block.namesFreshInRhsExprs] at hx
    simp only [List.cons_append, Block.namesFreshInRhsExprs]
    exact ⟨hx.1, ih hx.2⟩

mutual
/-- The empty name list is RHS-fresh in every statement. -/
theorem Stmt.namesFreshInRhsExprs_nil {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) :
    Stmt.namesFreshInRhsExprs (P := P) [] s := by
  cases s with
  | cmd c => cases c <;> (simp only [Stmt.namesFreshInRhsExprs]; exact List.Disjoint_nil_left _)
  | block lbl bss md =>
    simp only [Stmt.namesFreshInRhsExprs]; exact Block.namesFreshInRhsExprs_nil bss
  | ite g tss ess md =>
    simp only [Stmt.namesFreshInRhsExprs]
    exact ⟨Block.namesFreshInRhsExprs_nil tss, Block.namesFreshInRhsExprs_nil ess⟩
  | loop g m inv body md =>
    simp only [Stmt.namesFreshInRhsExprs]; exact Block.namesFreshInRhsExprs_nil body
  | exit lbl md => simp only [Stmt.namesFreshInRhsExprs]
  | funcDecl d md => simp only [Stmt.namesFreshInRhsExprs]
  | typeDecl t md => simp only [Stmt.namesFreshInRhsExprs]
  termination_by sizeOf s

theorem Block.namesFreshInRhsExprs_nil {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) :
    Block.namesFreshInRhsExprs (P := P) [] ss := by
  match ss with
  | [] => simp only [Block.namesFreshInRhsExprs]
  | s :: rest =>
    simp only [Block.namesFreshInRhsExprs]
    exact ⟨Stmt.namesFreshInRhsExprs_nil s, Block.namesFreshInRhsExprs_nil rest⟩
  termination_by sizeOf ss
end

mutual
/-- `namesFreshInRhsExprs` over a `cons` name list splits as the head-singleton
freshness and the tail freshness (each leaf `List.Disjoint (hd :: tl) vars`
splits as `hd ∉ vars ∧ List.Disjoint tl vars`). -/
theorem Stmt.namesFreshInRhsExprs_cons_names {P : PureExpr}
    [HasFvars P] (hd : P.Ident) (tl : List P.Ident) (s : Stmt P (Cmd P))
    (h_hd : Stmt.namesFreshInRhsExprs (P := P) [hd] s)
    (h_tl : Stmt.namesFreshInRhsExprs (P := P) tl s) :
    Stmt.namesFreshInRhsExprs (P := P) (hd :: tl) s := by
  cases s with
  | cmd c =>
    cases c <;>
      · simp only [Stmt.namesFreshInRhsExprs] at h_hd h_tl ⊢
        exact List.Disjoint_cons_left.mpr ⟨List.Disjoint_singleton_left.mp h_hd, h_tl⟩
  | block lbl bss md =>
    simp only [Stmt.namesFreshInRhsExprs] at h_hd h_tl ⊢
    exact Block.namesFreshInRhsExprs_cons_names hd tl bss h_hd h_tl
  | ite g tss ess md =>
    simp only [Stmt.namesFreshInRhsExprs] at h_hd h_tl ⊢
    exact ⟨Block.namesFreshInRhsExprs_cons_names hd tl tss h_hd.1 h_tl.1,
           Block.namesFreshInRhsExprs_cons_names hd tl ess h_hd.2 h_tl.2⟩
  | loop g m inv body md =>
    simp only [Stmt.namesFreshInRhsExprs] at h_hd h_tl ⊢
    exact Block.namesFreshInRhsExprs_cons_names hd tl body h_hd h_tl
  | exit lbl md => simp only [Stmt.namesFreshInRhsExprs]
  | funcDecl d md => simp only [Stmt.namesFreshInRhsExprs]
  | typeDecl t md => simp only [Stmt.namesFreshInRhsExprs]
  termination_by sizeOf s

theorem Block.namesFreshInRhsExprs_cons_names {P : PureExpr}
    [HasFvars P] (hd : P.Ident) (tl : List P.Ident) (ss : List (Stmt P (Cmd P)))
    (h_hd : Block.namesFreshInRhsExprs (P := P) [hd] ss)
    (h_tl : Block.namesFreshInRhsExprs (P := P) tl ss) :
    Block.namesFreshInRhsExprs (P := P) (hd :: tl) ss := by
  match ss with
  | [] => simp only [Block.namesFreshInRhsExprs]
  | s :: rest =>
    simp only [Block.namesFreshInRhsExprs] at h_hd h_tl ⊢
    exact ⟨Stmt.namesFreshInRhsExprs_cons_names hd tl s h_hd.1 h_tl.1,
           Block.namesFreshInRhsExprs_cons_names hd tl rest h_hd.2 h_tl.2⟩
  termination_by sizeOf ss
end

/-- Assemble `namesFreshInRhsExprs names ss` from per-name singleton facts. -/
theorem Block.namesFreshInRhsExprs_of_forall_mem {P : PureExpr}
    [HasFvars P] (names : List P.Ident) (ss : List (Stmt P (Cmd P)))
    (h : ∀ z ∈ names, Block.namesFreshInRhsExprs (P := P) [z] ss) :
    Block.namesFreshInRhsExprs (P := P) names ss := by
  induction names with
  | nil => exact Block.namesFreshInRhsExprs_nil ss
  | cons hd tl ih =>
    exact Block.namesFreshInRhsExprs_cons_names hd tl ss
      (h hd (List.mem_cons_self ..)) (ih (fun z hz => h z (List.mem_cons_of_mem _ hz)))

/-- The empty name list is fresh in every statement's expressions:
`namesFreshInExprs` is `List.Disjoint [] _`, which holds vacuously. -/
theorem Stmt.namesFreshInExprs_nil {P : PureExpr} [HasFvars P] (s : Stmt P (Cmd P)) :
    Stmt.namesFreshInExprs (P := P) [] s :=
  List.Disjoint_nil_left _

theorem Block.namesFreshInExprs_nil {P : PureExpr} [HasFvars P] (ss : List (Stmt P (Cmd P))) :
    Block.namesFreshInExprs (P := P) [] ss :=
  List.Disjoint_nil_left _

/-- Local helper: every `Q`-kind name is fresh in a read-var set, given that set
contains no `Q`-kind ident. -/
private theorem disjoint_of_shapefree_leaf {P : PureExpr} [HasIdent P]
    {Q : String → Prop} {names : List P.Ident} {vars : List P.Ident}
    (h_names_suffix : ∀ z ∈ names, ∃ str : String, z = HasIdent.ident str ∧ Q str)
    (h_sf : ∀ str : String, Q str → HasIdent.ident (P := P) str ∉ vars) :
    List.Disjoint names vars := by
  intro z hz hzv
  obtain ⟨str, h_eq, h_suf⟩ := h_names_suffix z hz
  exact (h_eq ▸ h_sf str h_suf) hzv

/-- `names` fresh in `s`'s expressions is now *definitionally* disjointness from
`s`'s read-var set `Stmt.getVars s`. -/
private theorem Stmt.namesFreshInExprs_of_disjoint_getVars {P : PureExpr}
    [HasIdent P] [HasFvars P] {names : List P.Ident}
    (s : Stmt P (Cmd P))
    (h : List.Disjoint names (Stmt.getVars s)) :
    Stmt.namesFreshInExprs names s := h

private theorem Block.namesFreshInExprs_of_disjoint_getVars {P : PureExpr}
    [HasIdent P] [HasFvars P] {names : List P.Ident}
    (ss : List (Stmt P (Cmd P)))
    (h : List.Disjoint names (Block.getVars ss)) :
    Block.namesFreshInExprs names ss := h

/-- `exprsShapeFree s` plus "every `names` element is a `Q`-kind ident"
implies `names` is fresh in `s`'s expressions. -/
private theorem Stmt.namesFreshInExprs_of_exprsShapeFree {P : PureExpr}
    [HasIdent P] [HasFvars P] {Q : String → Prop} {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ Q str)
    (s : Stmt P (Cmd P))
    (h : Stmt.exprsShapeFree (P := P) Q s) :
    Stmt.namesFreshInExprs names s :=
  Stmt.namesFreshInExprs_of_disjoint_getVars s
    (disjoint_of_shapefree_leaf h_names_suffix h)

private theorem Block.namesFreshInExprs_of_exprsShapeFree {P : PureExpr}
    [HasIdent P] [HasFvars P] {Q : String → Prop} {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ Q str)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.exprsShapeFree (P := P) Q ss) :
    Block.namesFreshInExprs names ss :=
  Block.namesFreshInExprs_of_disjoint_getVars ss
    (disjoint_of_shapefree_leaf h_names_suffix h)

/-- Public form: `exprsShapeFree ss` plus `Q`-kind `names` give freshness in
exprs.  Re-exported (non-`private`) so the `.loop` arm's `h_B_fresh` discharge
in the WF layer can consume it. -/
theorem Block.namesFreshInExprs_of_exprsShapeFree' {P : PureExpr}
    [HasIdent P] [HasFvars P] {Q : String → Prop} {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ Q str)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.exprsShapeFree (P := P) Q ss) :
    Block.namesFreshInExprs names ss :=
  Block.namesFreshInExprs_of_exprsShapeFree h_names_suffix ss h

/-! ### `exprsShapeFree` arm characterizations

`Stmt/Block.exprsShapeFree` are now defined flat over `Stmt.getVars`/`Block.getVars`.
These `iff`s recover the per-constructor recursive shape (matching how `getVars`
distributes over `++`/`flatMap`), so downstream proofs can reason arm-by-arm. -/

theorem Block.exprsShapeFree_nil {P : PureExpr} [HasIdent P] [HasFvars P]
    [HasVarsPure P (Cmd P)] {Q : String → Prop} :
    Block.exprsShapeFree (P := P) Q [] := by
  intro str _ hmem; simp only [Block.getVars] at hmem; exact absurd hmem List.not_mem_nil

theorem Block.exprsShapeFree_cons_iff {P : PureExpr} [HasIdent P] [HasFvars P]
    [HasVarsPure P (Cmd P)] {Q : String → Prop} {s : Stmt P (Cmd P)}
    {rest : List (Stmt P (Cmd P))} :
    Block.exprsShapeFree (P := P) Q (s :: rest) ↔
      Stmt.exprsShapeFree (P := P) Q s ∧ Block.exprsShapeFree (P := P) Q rest := by
  constructor
  · intro h
    exact ⟨fun str hQ hmem => h str hQ (by simp only [Block.getVars]; exact List.mem_append.mpr (Or.inl hmem)),
           fun str hQ hmem => h str hQ (by simp only [Block.getVars]; exact List.mem_append.mpr (Or.inr hmem))⟩
  · rintro ⟨h_s, h_rest⟩ str hQ hmem
    simp only [Block.getVars] at hmem
    rcases List.mem_append.mp hmem with hh | ht
    · exact h_s str hQ hh
    · exact h_rest str hQ ht

theorem Block.exprsShapeFree_singleton {P : PureExpr} [HasIdent P] [HasFvars P]
    [HasVarsPure P (Cmd P)] {Q : String → Prop} {s : Stmt P (Cmd P)} :
    Block.exprsShapeFree (P := P) Q [s] ↔ Stmt.exprsShapeFree (P := P) Q s :=
  Block.exprsShapeFree_cons_iff.trans (and_iff_left Block.exprsShapeFree_nil)

/-- `Block.exprsShapeFree Q` distributes over list append. -/
theorem Block.exprsShapeFree_append {P : PureExpr} [HasIdent P] [HasVarsPure P (Cmd P)] [HasFvars P] {Q : String → Prop}
    (xs ys : List (Stmt P (Cmd P)))
    (h : Block.exprsShapeFree (P := P) Q xs ∧ Block.exprsShapeFree (P := P) Q ys) :
    Block.exprsShapeFree (P := P) Q (xs ++ ys) := by
  induction xs with
  | nil => simpa only [List.nil_append] using h.2
  | cons x rest ih =>
      rw [List.cons_append, Block.exprsShapeFree_cons_iff]
      rw [Block.exprsShapeFree_cons_iff] at h
      exact ⟨h.1.1, ih ⟨h.1.2, h.2⟩⟩

theorem Stmt.exprsShapeFree_cmd {P : PureExpr} [HasIdent P] [HasFvars P]
    [HasVarsPure P (Cmd P)] {Q : String → Prop} {c : Cmd P} :
    Stmt.exprsShapeFree (P := P) Q (.cmd c) ↔
      (∀ str : String, Q str → HasIdent.ident (P := P) str ∉ Cmd.getVars c) := by
  constructor
  · intro h str hQ hmem
    exact h str hQ (by simp only [Stmt.getVars, HasVarsPure.getVars]; exact hmem)
  · intro h str hQ hmem
    simp only [Stmt.getVars, HasVarsPure.getVars] at hmem
    exact h str hQ hmem

theorem Stmt.exprsShapeFree_block {P : PureExpr} [HasIdent P] [HasFvars P]
    [HasVarsPure P (Cmd P)] {Q : String → Prop} {lbl : String}
    {bss : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.exprsShapeFree (P := P) Q (.block lbl bss md) ↔ Block.exprsShapeFree (P := P) Q bss := by
  constructor
  · intro h str hQ hmem; exact h str hQ (by simp only [Stmt.getVars]; exact hmem)
  · intro h str hQ hmem; simp only [Stmt.getVars] at hmem; exact h str hQ hmem

theorem Stmt.exprsShapeFree_ite {P : PureExpr} [HasIdent P] [HasFvars P]
    [HasVarsPure P (Cmd P)] {Q : String → Prop} {g : ExprOrNondet P}
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.exprsShapeFree (P := P) Q (.ite g tss ess md) ↔
      (∀ str : String, Q str → HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars g) ∧
      Block.exprsShapeFree (P := P) Q tss ∧ Block.exprsShapeFree (P := P) Q ess := by
  simp only [Stmt.exprsShapeFree, Block.exprsShapeFree, Stmt.getVars]
  constructor
  · intro h
    refine ⟨fun str hQ hmem => h str hQ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hmem)))),
            fun str hQ hmem => h str hQ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hmem)))),
            fun str hQ hmem => h str hQ (List.mem_append.mpr (Or.inr hmem))⟩
  · rintro ⟨h_g, h_t, h_e⟩ str hQ hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · rcases List.mem_append.mp h1 with hg | ht
      · exact h_g str hQ hg
      · exact h_t str hQ ht
    · exact h_e str hQ h2

theorem Stmt.exprsShapeFree_loop {P : PureExpr} [HasIdent P] [HasFvars P]
    [HasVarsPure P (Cmd P)] {Q : String → Prop} {g : ExprOrNondet P}
    {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P} :
    Stmt.exprsShapeFree (P := P) Q (.loop g m inv body md) ↔
      (∀ str : String, Q str → HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars g) ∧
      (∀ str : String, Q str → HasIdent.ident (P := P) str ∉ (m.map HasFvars.getFvars).getD []) ∧
      (∀ p ∈ inv, ∀ str : String, Q str → HasIdent.ident (P := P) str ∉ HasFvars.getFvars p.snd) ∧
      Block.exprsShapeFree (P := P) Q body := by
  simp only [Stmt.exprsShapeFree, Block.exprsShapeFree, Stmt.getVars]
  constructor
  · intro h
    refine ⟨fun str hQ hmem => h str hQ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hmem)))))),
            fun str hQ hmem => h str hQ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hmem)))))),
            fun p hp str hQ hmem => h str hQ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hmem⟩))))),
            fun str hQ hmem => h str hQ (List.mem_append.mpr (Or.inr hmem))⟩
  · rintro ⟨h_g, h_m, h_inv, h_body⟩ str hQ hmem
    rcases List.mem_append.mp hmem with h1 | hbody
    · rcases List.mem_append.mp h1 with h2 | hinv
      · rcases List.mem_append.mp h2 with hg | hm
        · exact h_g str hQ hg
        · exact h_m str hQ hm
      · obtain ⟨p, hp, hpmem⟩ := List.mem_flatMap.mp hinv
        exact h_inv p hp str hQ hpmem
    · exact h_body str hQ hbody

end -- public section

end Imperative
