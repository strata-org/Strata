/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt

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
  and `userBlockLabels` (the `_cons_iff` / `_branch_*` / `_loop_*` / `_block_*`
  families), plus the two non-structural results `exitsCoveredByBlocks_weaken`
  (label-list monotonicity) and `all_cmd_exitsCoveredByBlocks`.
- Distribution of the block-level walkers over `++`
  (`initVars`/`simpleShape`/`loopHasNoInvariants`/`modifiedVars`/
  `noInitsAnywhere`/`loopBodyNoInits`/`userBlockLabels`_append).
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
and `userBlockLabels`.  They accompany the `_append` distribution lemmas
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

theorem Block.userBlockLabels_block_cons {P : PureExpr} {C : Type}
    (l : String) (bss : List (Stmt P C)) (md : MetaData P)
    (rest : List (Stmt P C)) :
    Block.userBlockLabels (.block l bss md :: rest) =
      (l :: Block.userBlockLabels bss) ++ Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_ite_cons {P : PureExpr} {C : Type}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P C))
    (md : MetaData P) (rest : List (Stmt P C)) :
    Block.userBlockLabels (.ite c tss ess md :: rest) =
      (Block.userBlockLabels tss ++ Block.userBlockLabels ess)
        ++ Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_loop_cons {P : PureExpr} {C : Type}
    (c : Imperative.ExprOrNondet P) (m : Option P.Expr)
    (is : List (String × P.Expr)) (bss : List (Stmt P C))
    (md : MetaData P) (rest : List (Stmt P C)) :
    Block.userBlockLabels (.loop c m is bss md :: rest) =
      Block.userBlockLabels bss ++ Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_cmd_cons {P : PureExpr} {C : Type}
    (c : C) (rest : List (Stmt P C)) :
    Block.userBlockLabels (.cmd c :: rest) = Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

/-! # `userBlockLabels` is preserved by `nondetElim`

The structured-to-structured pass `Block.nondetElim` (eliminates
nondeterministic control) preserves the multiset *and order* of user-provided
`.block` labels: every label is carried through verbatim, and the only freshly
generated statements are `.cmd`s (which `userBlockLabels` ignores). Hence the
source-side well-formedness condition `userLabelsShapeNodup ss` (a function of
`userBlockLabels ss`) survives the pass. -/

/-! ## Distributivity helpers for `userBlockLabels`

`userBlockLabels` is a list-valued structural walk, so the per-constructor
`_out`/havoc-prefix lemmas of the pass (which split via `++` and
`List.map Stmt.cmd`) need these two distributivity facts. -/

/-- `userBlockLabels` of the empty block is empty. -/
theorem Block.userBlockLabels_nil {P : PureExpr} {C : Type} :
    Block.userBlockLabels ([] : List (Stmt P C)) = [] := rfl

/-- `userBlockLabels` distributes over list concatenation. -/
theorem Block.userBlockLabels_append {P : PureExpr} {C : Type}
    (ss₁ ss₂ : List (Stmt P C)) :
    Block.userBlockLabels (ss₁ ++ ss₂) =
      Block.userBlockLabels ss₁ ++ Block.userBlockLabels ss₂ := by
  induction ss₁ with
  | nil => simp [Block.userBlockLabels]
  | cons s rest ih =>
      simp only [List.cons_append, Block.userBlockLabels, ih, List.append_assoc]

/-- A list of `.cmd` statements contributes no user block labels. -/
theorem Block.userBlockLabels_map_cmd {P : PureExpr} {C : Type}
    (cs : List C) :
    Block.userBlockLabels (cs.map (@Stmt.cmd P C)) = ([] : List String) := by
  induction cs with
  | nil => simp [Block.userBlockLabels]
  | cons c rest ih =>
      simp only [List.map_cons]
      rw [Block.userBlockLabels_cmd_cons, ih]

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

end -- public section

end Imperative
