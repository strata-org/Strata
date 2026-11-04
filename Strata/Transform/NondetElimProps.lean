/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElim
public import Strata.DL.Imperative.CmdProps
public import Strata.Languages.Core.StmtExtendCallBridgeProps
import Strata.DL.Imperative.StmtProps
import all Strata.Util.ListUtilsProps
import all Strata.DL.Util.StringGen

public section

namespace Imperative

open LabelGen (StringGenM)

/-! # `nondetElim` structural metatheory

Output-projection (`*_out`) and shape-preservation theorems for the
`nondetElim` pass. These are structural properties of the `Stmt.nondetElimM` /
`Block.nondetElimM` definitions in `NondetElim.lean`; the soundness results live
in `NondetElimCorrect.lean`.

Key results:
  * Output projections — `Stmt.nondetElimM_block_out`,
    `Stmt.nondetElimM_ite_det_out`, `Stmt.nondetElimM_ite_nondet_out`,
    `Stmt.nondetElimM_loop_det_out`, `Stmt.nondetElimM_loop_nondet_out`,
    `Block.nondetElimM_cons_out`: equational normal forms for one pass step.
  * Shape preservation — `nondetElim_loopHasNoInvariants`,
    `nondetElim_noMeasureLoops`, and `nondetElim_noNondetGuards` (top-level, over
    `Block.nondetElim`), each built from the corresponding mutual
    `Stmt`/`Block.nondetElimM_*` pair (`nondetElim_noNondetGuards` from the
    command-generic `Stmt`/`Block.nondetElimM_noNondetGuards` pair).
  * Generator advance — `Stmt.nondetElimM_genStep` / `Block.nondetElimM_genStep`:
    the pass advances the `StringGenState` by a `GenStep`.
  * Core call-extension bridge — `Stmt.nondetElimM_isNotCall` and
    `Block.nondetElimM_isNotCall` preserve call-freeness, while
    `embedStmt_nondetElimM`, `embedStmts_nondetElimM`, and
    `embedStmts_nondetElim` commute rewriting with base-command embedding.
  * Def-use preservation — `Stmt.nondetElimM_defUseWellFormed` /
    `Block.nondetElimM_defUseWellFormed` (mutual) and the top-level
    `Block.nondetElim_defUseWellFormed`: rewriting a def-use well-formed block
    yields def-use well-formed output, tracking generated guard registers
    through the `NondetElimDefinedRel` defined-register relation. -/

section Projections

/-- Output projection, generic over the command type: rewriting a `.block`
statement yields the single block statement whose body is the rewritten body. -/
theorem Stmt.nondetElimM_block_out {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (lbl : String) (bss : List (Stmt P CmdT)) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.block lbl bss md) σ).1 =
      [Stmt.block lbl (Block.nondetElimM bss σ).1 md] := by
  rw [Stmt.nondetElimM]
  rcases h : Block.nondetElimM bss σ with ⟨bss', σ'⟩
  simp only [h]

/-- Output projection, generic over the command type: rewriting a
deterministic-guard `.ite` yields the single `.ite` on the same guard with both
branches rewritten, the else branch threading the generator state left by the
then branch. -/
theorem Stmt.nondetElimM_ite_det_out {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (e : P.Expr) (tss ess : List (Stmt P CmdT)) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite (.det e) tss ess md) σ).1 =
      [Stmt.ite (.det e) (Block.nondetElimM tss σ).1
        (Block.nondetElimM ess (Block.nondetElimM tss σ).2).1 md] := by
  rw [Stmt.nondetElimM]
  rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
  rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
  simp only [h₁, h₂]

/-- Output projection, generic over the command type: rewriting a
nondeterministic-guard `.ite` yields a freshly generated boolean guard `init`
followed by a deterministic `.ite` on that guard with both branches rewritten. -/
theorem Stmt.nondetElimM_ite_nondet_out {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (tss ess : List (Stmt P CmdT)) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite .nondet tss ess md) σ).1 =
      let g := (StringGenState.gen NondetElim.prefixIte σ).1
      let ident := HasIdent.ident (P := P) g
      let σ₁ := (StringGenState.gen NondetElim.prefixIte σ).2
      [Stmt.cmd (HasInit.init ident HasBool.boolTy .nondet md),
       Stmt.ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) (Block.nondetElimM tss σ₁).1
         (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md] := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen NondetElim.prefixIte σ with ⟨g, σ₁⟩
  rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
  rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
  simp only [hg, h₁, h₂]

/-- Output projection, generic over the command type: rewriting a
deterministic-guard `.loop` yields the single `.loop` on the same guard, measure,
and invariants with its body rewritten. -/
theorem Stmt.nondetElimM_loop_det_out {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (e : P.Expr) (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P CmdT)) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop (.det e) m inv body md) σ).1 =
      [Stmt.loop (.det e) m inv (Block.nondetElimM body σ).1 md] := by
  rw [Stmt.nondetElimM]
  rcases h : Block.nondetElimM body σ with ⟨body', σ'⟩
  simp only [h]

/-- Output projection, generic over the command type: rewriting a
nondeterministic-guard `.loop` yields a freshly generated boolean guard `init`
followed by a deterministic `.loop` on that guard whose body is the rewritten
body with a trailing guard `havoc`. -/
theorem Stmt.nondetElimM_loop_nondet_out {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P CmdT)) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop .nondet m inv body md) σ).1 =
      let g := (StringGenState.gen NondetElim.prefixLoop σ).1
      let ident := HasIdent.ident (P := P) g
      let σ₁ := (StringGenState.gen NondetElim.prefixLoop σ).2
      [Stmt.cmd (HasInit.init ident HasBool.boolTy .nondet md),
       Stmt.loop (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) m inv
         ((Block.nondetElimM body σ₁).1 ++ [Stmt.cmd (HasHavoc.havoc ident md)]) md] := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen NondetElim.prefixLoop σ with ⟨g, σ₁⟩
  rcases h : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
  simp only [hg, h]

/-- Output projection, generic over the command type: rewriting a cons block
`s :: rest` concatenates the rewrite of `s` with the rewrite of `rest` run on the
generator state that `s` leaves behind. -/
theorem Block.nondetElimM_cons_out {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (s : Stmt P CmdT) (rest : List (Stmt P CmdT)) (σ : StringGenState) :
    (Block.nondetElimM (s :: rest) σ).1 =
      (Stmt.nondetElimM s σ).1 ++
        (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).1 := by
  rw [Block.nondetElimM]
  rcases h₁ : Stmt.nondetElimM s σ with ⟨ss_s, σ₁⟩
  rcases h₂ : Block.nondetElimM rest σ₁ with ⟨ss_r, σ₂⟩
  simp only [h₁, h₂]

end Projections

section Preservation

mutual
/-- `Stmt.nondetElimM` preserves `loopHasNoInvariants`: the rewrite passes loop
invariant lists through unchanged and adds no labeled-invariant loops. -/
theorem Stmt.nondetElimM_loopHasNoInvariants {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.loopHasNoInvariants s = true) :
    Block.loopHasNoInvariants (Stmt.nondetElimM s σ).1 = true := by
  match s with
  | .cmd c => simp [Stmt.nondetElimM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true]
      rw [Stmt.loopHasNoInvariants] at h
      exact Block.nondetElimM_loopHasNoInvariants bss σ h
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true,
                 Block.nondetElimM_loopHasNoInvariants tss σ h.1,
                 Block.nondetElimM_loopHasNoInvariants ess _ h.2]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true,
                 Block.nondetElimM_loopHasNoInvariants tss _ h.1,
                 Block.nondetElimM_loopHasNoInvariants ess _ h.2]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true,
                 h.1, Block.nondetElimM_loopHasNoInvariants body σ h.2]
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h
      simp only [Block.loopHasNoInvariants_append, Block.loopHasNoInvariants,
                 Stmt.loopHasNoInvariants, Bool.and_true, h.1,
                 Block.nondetElimM_loopHasNoInvariants body _ h.2]
  | .exit lbl md => simp [Stmt.nondetElimM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .typeDecl t md => simp [Stmt.nondetElimM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  termination_by sizeOf s

theorem Block.nondetElimM_loopHasNoInvariants {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.loopHasNoInvariants ss = true) :
    Block.loopHasNoInvariants (Block.nondetElimM ss σ).1 = true := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.loopHasNoInvariants]
  | s :: rest =>
      rw [Block.loopHasNoInvariants, Bool.and_eq_true] at h
      rw [Block.nondetElimM_cons_out, Block.loopHasNoInvariants_append]
      simp only [Stmt.nondetElimM_loopHasNoInvariants s σ h.1,
                 Block.nondetElimM_loopHasNoInvariants rest _ h.2, Bool.and_true]
  termination_by sizeOf ss
end

mutual
/-- `Stmt.nondetElimM` preserves `noMeasureLoops`: the rewrite passes loop
measures through unchanged and adds no measured loops. -/
theorem Stmt.nondetElimM_noMeasureLoops {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.noMeasureLoops s = true) :
    Block.noMeasureLoops (Stmt.nondetElimM s σ).1 = true := by
  match s with
  | .cmd c => simp [Stmt.nondetElimM, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Block.noMeasureLoops, Stmt.noMeasureLoops, Bool.and_true]
      rw [Stmt.noMeasureLoops] at h
      exact Block.nondetElimM_noMeasureLoops bss σ h
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      rw [Stmt.noMeasureLoops, Bool.and_eq_true] at h
      simp only [Block.noMeasureLoops, Stmt.noMeasureLoops, Bool.and_true,
                 Block.nondetElimM_noMeasureLoops tss σ h.1,
                 Block.nondetElimM_noMeasureLoops ess _ h.2]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      rw [Stmt.noMeasureLoops, Bool.and_eq_true] at h
      simp only [Block.noMeasureLoops, Stmt.noMeasureLoops, Bool.and_true,
                 Block.nondetElimM_noMeasureLoops tss _ h.1,
                 Block.nondetElimM_noMeasureLoops ess _ h.2]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      rw [Stmt.noMeasureLoops, Bool.and_eq_true] at h
      simp only [Block.noMeasureLoops, Stmt.noMeasureLoops, Bool.and_true,
                 h.1, Block.nondetElimM_noMeasureLoops body σ h.2]
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      rw [Stmt.noMeasureLoops, Bool.and_eq_true] at h
      simp only [Block.noMeasureLoops_append, Block.noMeasureLoops,
                 Stmt.noMeasureLoops, Bool.and_true, h.1,
                 Block.nondetElimM_noMeasureLoops body _ h.2]
  | .exit lbl md => simp [Stmt.nondetElimM, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .typeDecl t md => simp [Stmt.nondetElimM, Block.noMeasureLoops, Stmt.noMeasureLoops]
  termination_by sizeOf s

theorem Block.nondetElimM_noMeasureLoops {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.noMeasureLoops ss = true) :
    Block.noMeasureLoops (Block.nondetElimM ss σ).1 = true := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.noMeasureLoops]
  | s :: rest =>
      rw [Block.noMeasureLoops, Bool.and_eq_true] at h
      rw [Block.nondetElimM_cons_out, Block.noMeasureLoops_append]
      simp only [Stmt.nondetElimM_noMeasureLoops s σ h.1,
                 Block.nondetElimM_noMeasureLoops rest _ h.2, Bool.and_true]
  termination_by sizeOf ss
end

/-- Top-level preservation: `Block.nondetElim` preserves `loopHasNoInvariants`. -/
theorem nondetElim_loopHasNoInvariants {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (h : Block.loopHasNoInvariants ss = true) :
    Block.loopHasNoInvariants (Block.nondetElim ss) = true :=
  Block.nondetElimM_loopHasNoInvariants ss StringGenState.emp h

/-- Top-level preservation: `Block.nondetElim` preserves `noMeasureLoops`. -/
theorem nondetElim_noMeasureLoops {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (h : Block.noMeasureLoops ss = true) :
    Block.noMeasureLoops (Block.nondetElim ss) = true :=
  Block.nondetElimM_noMeasureLoops ss StringGenState.emp h

mutual
/-- The pass advances the generator state by a `GenStep`: it only ever calls
`StringGenState.gen` (which is a `GenStep`), so well-formedness is preserved and
the generated-labels list only grows. -/
theorem Stmt.nondetElimM_genStep {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 := by
  match s with
  | .cmd c => simp only [Stmt.nondetElimM]; exact StringGenState.GenStep.refl _
  | .block lbl bss md =>
      rw [Stmt.nondetElimM]
      rcases h : Block.nondetElimM bss σ with ⟨bss', σ'⟩
      simp only [h]
      have := Block.nondetElimM_genStep bss σ
      rw [h] at this; exact this
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM]
      rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
      rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
      simp only [h₁, h₂]
      have g₁ := Block.nondetElimM_genStep tss σ
      have g₂ := Block.nondetElimM_genStep ess σ₁
      rw [h₁] at g₁; rw [h₂] at g₂
      exact StringGenState.GenStep.trans g₁ g₂
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM]
      rcases hg : StringGenState.gen NondetElim.prefixIte σ with ⟨g, σ₁⟩
      rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
      rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
      simp only [hg, h₁, h₂]
      have g₀ : StringGenState.GenStep σ σ₁ := by
        have := StringGenState.GenStep.of_gen NondetElim.prefixIte σ; rw [hg] at this; exact this
      have g₁ := Block.nondetElimM_genStep tss σ₁
      have g₂ := Block.nondetElimM_genStep ess σ₂
      rw [h₁] at g₁; rw [h₂] at g₂
      exact StringGenState.GenStep.trans g₀ (StringGenState.GenStep.trans g₁ g₂)
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM]
      rcases h : Block.nondetElimM body σ with ⟨body', σ'⟩
      simp only [h]
      have := Block.nondetElimM_genStep body σ
      rw [h] at this; exact this
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM]
      rcases hg : StringGenState.gen NondetElim.prefixLoop σ with ⟨g, σ₁⟩
      rcases h : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
      simp only [hg, h]
      have g₀ : StringGenState.GenStep σ σ₁ := by
        have := StringGenState.GenStep.of_gen NondetElim.prefixLoop σ; rw [hg] at this; exact this
      have g₁ := Block.nondetElimM_genStep body σ₁
      rw [h] at g₁
      exact StringGenState.GenStep.trans g₀ g₁
  | .exit lbl md => simp only [Stmt.nondetElimM]; exact StringGenState.GenStep.refl _
  | .typeDecl t md => simp only [Stmt.nondetElimM]; exact StringGenState.GenStep.refl _
  termination_by sizeOf s

theorem Block.nondetElimM_genStep {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    StringGenState.GenStep σ (Block.nondetElimM ss σ).2 := by
  match ss with
  | [] => simp only [Block.nondetElimM]; exact StringGenState.GenStep.refl _
  | s :: rest =>
      rw [Block.nondetElimM]
      rcases h₁ : Stmt.nondetElimM s σ with ⟨ss_s, σ₁⟩
      rcases h₂ : Block.nondetElimM rest σ₁ with ⟨ss_r, σ₂⟩
      simp only [h₁, h₂]
      have g₁ := Stmt.nondetElimM_genStep s σ
      have g₂ := Block.nondetElimM_genStep rest σ₁
      rw [h₁] at g₁; rw [h₂] at g₂
      exact StringGenState.GenStep.trans g₁ g₂
  termination_by sizeOf ss
end

end Preservation

end Imperative

public section

namespace Imperative

open LabelGen (StringGenM)

/-! ## `nondetElim` output has no nondeterministic guards

The one-step output projections (`Stmt.nondetElimM_*_out`,
`Block.nondetElimM_cons_out`, proved above) and the `++`-distribution lemmas
(`Block.noNondetGuards_append`, in `StmtProps`) are all generic over the command
type, so this proof applies at any `CmdT` — in particular at Core's `CmdExt`
command. -/

mutual
/-- The rewrite of any single statement (generic over the command type) has no
nondeterministic guard: every nondeterministic `ite`/`loop` is replaced by a
deterministic one guarded by a generated boolean. -/
theorem Stmt.nondetElimM_noNondetGuards {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (s : Stmt P CmdT) (σ : StringGenState) :
    Block.noNondetGuards (Stmt.nondetElimM s σ).1 = true := by
  match s with
  | .cmd c => simp [Stmt.nondetElimM, Block.noNondetGuards, Stmt.noNondetGuards]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Block.noNondetGuards, Stmt.noNondetGuards, Bool.and_true]
      exact Block.nondetElimM_noNondetGuards bss σ
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      simp only [Block.noNondetGuards, Stmt.noNondetGuards, Bool.and_true,
                 Block.nondetElimM_noNondetGuards tss σ,
                 Block.nondetElimM_noNondetGuards ess _]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      simp only [Block.noNondetGuards, Stmt.noNondetGuards, Bool.and_true,
                 Block.nondetElimM_noNondetGuards tss _,
                 Block.nondetElimM_noNondetGuards ess _]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      simp only [Block.noNondetGuards, Stmt.noNondetGuards, Bool.and_true]
      exact Block.nondetElimM_noNondetGuards body σ
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      simp only [Block.noNondetGuards, Stmt.noNondetGuards, Block.noNondetGuards_append,
                 Bool.and_true, Block.nondetElimM_noNondetGuards body _]
  | .exit lbl md => simp [Stmt.nondetElimM, Block.noNondetGuards, Stmt.noNondetGuards]
  | .typeDecl t md => simp [Stmt.nondetElimM, Block.noNondetGuards, Stmt.noNondetGuards]
  termination_by sizeOf s

/-- The rewrite of any block (generic over the command type) has no
nondeterministic guard. -/
theorem Block.nondetElimM_noNondetGuards {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (ss : List (Stmt P CmdT)) (σ : StringGenState) :
    Block.noNondetGuards (Block.nondetElimM ss σ).1 = true := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.noNondetGuards]
  | s :: rest =>
      rw [Block.nondetElimM_cons_out, Block.noNondetGuards_append]
      simp only [Stmt.nondetElimM_noNondetGuards s σ,
                 Block.nondetElimM_noNondetGuards rest _, Bool.and_true]
  termination_by sizeOf ss
end

/-- Top-level: the generic `Block.nondetElim` output has no nondeterministic
guards, at any command type. -/
theorem nondetElim_noNondetGuards {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (ss : List (Stmt P CmdT)) :
    Block.noNondetGuards (Block.nondetElim ss) = true :=
  Block.nondetElimM_noNondetGuards ss StringGenState.emp

end Imperative

public section

namespace Imperative


open LabelGen (StringGenM)

/-! ### Source-shape precondition

The simulation is only sound for source programs that never `init`/`set` a
gen-shaped (`HasUnderscoreDigitSuffix`) variable.  This is carried as an
explicit assumption: the front-ends feeding this pipeline never write such
names, and a source program that re-`init`s a parent-scoped variable inside a
loop body is already stuck under the existing semantics, independent of this
pass.  Without it the theorem is false — a pass-through source
`.cmd (set "$g_0" .nondet)` defines a gen-shaped slot, after which a later
`.ite .nondet`'s inserted `init $g := *` would collide and be stuck.

We carry it as "no `Q`-kind identifier appears among the block's defined +
modified variables" (mirroring the analogous threaded freshness obligation on
`definedVars ++ initVars` / `modifiedVars`).  Membership in `++` distributes
the obligation across sequencing and recursion automatically. -/

/-- The source-shape precondition over a source block: no statement in `ss`
ever defines or modifies a `Q`-kind variable. -/
@[expose] def SrcNoGenWrites {P : PureExpr} [HasFvars P] [HasIdent P]
    (Q : String → Prop)
    (ss : List (Stmt P (Cmd P))) : Prop :=
  (∀ s : String, Q s → HasIdent.ident (P := P) s ∉
    (Block.definedVars ss false ++ Block.modifiedVars ss))

/-- Every guard name generated under either `nondetElim` prefix satisfies
`NondetElim.isGeneratedName`. -/
theorem NondetElim.isGeneratedName_gen :
    (∀ sg, NondetElim.isGeneratedName (StringGenState.gen NondetElim.prefixIte sg).1)
  ∧ (∀ sg, NondetElim.isGeneratedName (StringGenState.gen NondetElim.prefixLoop sg).1) := by
  refine ⟨fun sg => ?_, fun sg => ?_⟩
  · exact Or.inl ⟨sg, rfl⟩
  · exact Or.inr ⟨sg, rfl⟩

section NondetElimStructuralState
variable {P : PureExpr}

/-- Rewriting a `.block` leaves the generator state produced by rewriting its
body. -/
theorem Stmt.nondetElimM_block_state [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] (lbl : String) (bss : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.block lbl bss md) σ).2 = (Block.nondetElimM bss σ).2 := by
  rw [Stmt.nondetElimM]; rcases h : Block.nondetElimM bss σ with ⟨bss', σ'⟩; simp only [h]

/-- Rewriting a deterministic `.ite` threads the state left by the then-branch
through the else-branch and returns the latter's state. -/
theorem Stmt.nondetElimM_ite_det_state [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] (e : P.Expr) (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite (.det e) tss ess md) σ).2 =
      (Block.nondetElimM ess (Block.nondetElimM tss σ).2).2 := by
  rw [Stmt.nondetElimM]
  rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
  rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
  simp only [h₁, h₂]

/-- Rewriting a nondeterministic `.ite` allocates its guard, then threads the
resulting state through the then- and else-branches in order. -/
theorem Stmt.nondetElimM_ite_nondet_state [HasIdent P] [HasFvar P]
    [HasFvars P] [HasBool P] (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2 =
      (Block.nondetElimM ess
        (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).2).2 := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen NondetElim.prefixIte σ with ⟨g, σ₁⟩
  rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
  rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
  simp only [hg, h₁, h₂]

/-- Rewriting a deterministic `.loop` leaves the generator state produced by
rewriting its body. -/
theorem Stmt.nondetElimM_loop_det_state [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] (e : P.Expr) (m : Option P.Expr)
    (inv : List (String × P.Expr)) (body : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop (.det e) m inv body md) σ).2 = (Block.nondetElimM body σ).2 := by
  rw [Stmt.nondetElimM]; rcases h : Block.nondetElimM body σ with ⟨body', σ'⟩; simp only [h]

/-- Rewriting a nondeterministic `.loop` allocates its guard and returns the
state produced by rewriting the body from that advanced state. -/
theorem Stmt.nondetElimM_loop_nondet_state [HasIdent P] [HasFvar P]
    [HasFvars P] [HasBool P] (m : Option P.Expr)
    (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 =
      (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2 := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen NondetElim.prefixLoop σ with ⟨g, σ₁⟩
  rcases h : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
  simp only [hg, h]

/-- Rewriting a cons block threads the state left by the head statement into
the rewrite of the remaining statements and returns the rest's state. -/
theorem Block.nondetElimM_cons_state [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P)))
    (σ : StringGenState) :
    (Block.nondetElimM (s :: rest) σ).2 = (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := by
  rw [Block.nondetElimM]
  rcases h₁ : Stmt.nondetElimM s σ with ⟨ss_s, σ₁⟩
  rcases h₂ : Block.nondetElimM rest σ₁ with ⟨ss_r, σ₂⟩
  simp only [h₁, h₂]

end NondetElimStructuralState

@[expose] def NondetElimDefinedRel {P : PureExpr} [HasIdent P]
    (σ : StringGenState) (source target : P.Ident → Bool) : Prop :=
  (∀ s, NondetElim.isGeneratedName s → source (HasIdent.ident (P := P) s) = false) ∧
  (∀ s, NondetElim.isGeneratedName s → s ∉ σ.stringGens →
    target (HasIdent.ident (P := P) s) = false) ∧
  (∀ x, (∀ s, NondetElim.isGeneratedName s → x ≠ HasIdent.ident (P := P) s) →
    target x = source x)

namespace NondetElimDefinedRel

variable {P : PureExpr} [HasIdent P] [LawfulHasIdent P] [DecidableEq P.Ident]

omit [LawfulHasIdent P] [DecidableEq P.Ident] in
/-- Under the defined-register relation, every source-defined register is
target-defined; the relation only adds generated guard names to the target. -/
private theorem target_true {σ : StringGenState} {source target : P.Ident → Bool}
    (h : NondetElimDefinedRel σ source target) {x : P.Ident}
    (hx : source x = true) : target x = true := by
  classical
  by_cases hk : ∃ s, NondetElim.isGeneratedName s ∧ x = HasIdent.ident (P := P) s
  · obtain ⟨s, hs, rfl⟩ := hk
    rw [h.1 s hs] at hx
    contradiction
  · rw [h.2.2 x (by
      intro s hs heq
      exact hk ⟨s, hs, heq⟩)]
    exact hx

omit [LawfulHasIdent P] [DecidableEq P.Ident] in
/-- The defined-register relation is preserved as the generator state advances:
the wider set of generated names stays excluded from the target. -/
private theorem mono {σ σ' : StringGenState} {source target : P.Ident → Bool}
    (hstep : StringGenState.GenStep σ σ')
    (h : NondetElimDefinedRel σ source target) :
    NondetElimDefinedRel σ' source target := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro s hs hn
  exact h.2.1 s hs (fun hm => hn (hstep.subset hm))

omit [LawfulHasIdent P] in
/-- The defined-register relation is preserved by adding the same batch of
non-generated names to both the source and target defined sets. -/
private theorem add_nonKind {σ : StringGenState} {source target : P.Ident → Bool}
    (h : NondetElimDefinedRel σ source target) (xs : List P.Ident)
    (hxs : ∀ s, NondetElim.isGeneratedName s → HasIdent.ident (P := P) s ∉ xs) :
    NondetElimDefinedRel σ
      (fun x => source x || decide (x ∈ xs))
      (fun x => target x || decide (x ∈ xs)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    simp only
    rw [h.1 s hs]
    simp [hxs s hs]
  · intro s hs hn
    simp only
    rw [h.2.1 s hs hn]
    simp [hxs s hs]
  · intro x hx
    simp only
    rw [h.2.2 x hx]

/-- The defined-register relation is preserved by generating one fresh guard and
marking it defined on the target side only. -/
private theorem add_guard {σ : StringGenState} {source target : P.Ident → Bool}
    (h : NondetElimDefinedRel σ source target) (pf : String)
    (hkind : NondetElim.isGeneratedName (StringGenState.gen pf σ).1) :
    NondetElimDefinedRel (StringGenState.gen pf σ).2 source
      (fun x => target x || decide
        (x = HasIdent.ident (P := P) (StringGenState.gen pf σ).1)) := by
  let g := (StringGenState.gen pf σ).1
  refine ⟨h.1, ?_, ?_⟩
  · intro s hs hn
    have hsold : s ∉ σ.stringGens := by
      intro hm
      exact hn ((StringGenState.GenStep.of_gen pf σ).subset hm)
    have hsne : HasIdent.ident (P := P) s ≠ HasIdent.ident (P := P) g := by
      intro heq
      apply hn
      rw [StringGenState.stringGens_gen, List.mem_cons]
      exact Or.inl (LawfulHasIdent.ident_inj heq)
    have hsne' : HasIdent.ident (P := P) s ≠
        HasIdent.ident (P := P) (StringGenState.gen pf σ).1 := by
      simpa only [g] using hsne
    simp only
    rw [h.2.1 s hs hsold]
    simp [hsne']
  · intro x hx
    have hxg : x ≠ HasIdent.ident (P := P) g := hx g hkind
    have hxg' : x ≠ HasIdent.ident (P := P) (StringGenState.gen pf σ).1 := by
      simpa only [g] using hxg
    simp only
    rw [h.2.2 x hx]
    simp [hxg']

end NondetElimDefinedRel

/-- If every register in a list is source-defined, then under the
defined-register relation every register is target-defined. -/
private theorem all_target_true {P : PureExpr} [HasIdent P] [LawfulHasIdent P]
    [DecidableEq P.Ident]
    {σ : StringGenState} {source target : P.Ident → Bool}
    (hrel : NondetElimDefinedRel σ source target)
    {xs : List P.Ident} (hxs : xs.all source = true) :
    xs.all target = true := by
  rw [List.all_eq_true] at hxs ⊢
  intro x hx
  exact NondetElimDefinedRel.target_true hrel (hxs x hx)

mutual

/-- The pass preserves def-use well-formedness: rewriting a def-use well-formed
statement under a defined-register relation yields def-use well-formed output and
extends the relation by the statement's newly defined variables. -/
theorem Stmt.nondetElimM_defUseWellFormed {P : PureExpr}
    [HasIdent P] [LawfulHasIdent P] [DecidableEq P.Ident]
    [HasFvar P] [HasFvars P] [LawfulHasFvars P]
    [HasBool P] [HasOps P]
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (source target declaredSource declaredTarget : P.Ident → Bool)
    (hrel : NondetElimDefinedRel σ source target)
    (hwf : StringGenState.WF σ)
    (hdecl : ∀ x, declaredSource x = true → declaredTarget x = true)
    (hfvarops : ∀ x, HasOps.getOps
      (HasFvar.mkTypedFvar (P := P) x HasBool.boolTy) = [])
    (hdu : Stmt.defUseWellFormed source declaredSource s = true)
    (hnogen : ∀ str, NondetElim.isGeneratedName str →
      HasIdent.ident (P := P) str ∉
        (Stmt.definedVars s false ++ Stmt.modifiedVars s)) :
    Block.defUseWellFormed target declaredTarget (Stmt.nondetElimM s σ).1 = true ∧
    NondetElimDefinedRel (Stmt.nondetElimM s σ).2
      (fun x => source x || decide (x ∈ Stmt.definedVars s true))
      (fun x => target x || decide
        (x ∈ Block.definedVars (Stmt.nondetElimM s σ).1 true)) := by
  match s with
  | .cmd c =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      have hdefs : ∀ str, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉
            HasVarsImp.definedVars (P := P) c true := by
        intro str hs hm
        apply hnogen str hs
        apply List.mem_append_left
        with_unfolding_all exact hm
      have hcmd : Stmt.defUseWellFormed target declaredTarget (.cmd c) = true := by
        simp only [Stmt.defUseWellFormed, Bool.and_eq_true]
        exact ⟨⟨⟨all_target_true hrel hdu.1.1.1,
          all_target_true hrel hdu.1.1.2⟩,
          by
            have hdall := hdu.1.2
            rw [List.all_eq_true] at hdall ⊢
            intro x hx
            have hnk : ∀ str, NondetElim.isGeneratedName str →
                x ≠ HasIdent.ident (P := P) str := by
              intro str hs heq
              exact hdefs str hs (heq ▸ hx)
            rw [hrel.2.2 x hnk]
            exact hdall x hx⟩,
          List.all_mono hdecl hdu.2⟩
      refine ⟨?_, ?_⟩
      · simpa [Stmt.nondetElimM, Block.defUseWellFormed] using hcmd
      · rw [Stmt.nondetElimM]
        simp only [Stmt.definedVars, Block.definedVars, List.append_nil]
        change NondetElimDefinedRel σ
          (fun x => source x || decide
            (x ∈ HasVarsImp.definedVars (P := P) c true))
          (fun x => target x || decide
            (x ∈ HasVarsImp.definedVars (P := P) c true))
        exact NondetElimDefinedRel.add_nonKind hrel
          (HasVarsImp.definedVars (P := P) c true) hdefs
  | .block lbl bss md =>
      have hng : SrcNoGenWrites NondetElim.isGeneratedName bss := by
        intro str hs hm
        exact hnogen str hs (by simpa [Stmt.definedVars, Stmt.modifiedVars] using hm)
      obtain ⟨hbody, _⟩ := Block.nondetElimM_defUseWellFormed bss σ source target
        declaredSource declaredTarget hrel hwf hdecl hfvarops hdu hng
      refine ⟨?_, ?_⟩
      · rw [Stmt.nondetElimM_block_out]
        simpa [Block.defUseWellFormed, Stmt.defUseWellFormed] using hbody
      · rw [Stmt.nondetElimM_block_state, Stmt.nondetElimM_block_out]
        simp only [Stmt.definedVars, Block.definedVars,
          ↓reduceIte, List.append_nil]
        have hsource : (fun x => source x || decide (x ∈ ([] : List P.Ident))) = source := by
          funext x
          simp
        have htarget : (fun x => target x || decide (x ∈ ([] : List P.Ident))) = target := by
          funext x
          simp
        rw [hsource, htarget]
        exact
          NondetElimDefinedRel.mono (Block.nondetElimM_genStep bss σ) hrel
  | .ite (.det e) tss ess md =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      have hngt : SrcNoGenWrites NondetElim.isGeneratedName tss := by
        intro str hs hm
        rcases List.mem_append.mp hm with hd | hm
        · exact hnogen str hs (List.mem_append_left _ (by
            simp only [Stmt.definedVars, Bool.false_eq_true, ite_false, List.mem_append]
            exact Or.inl hd))
        · exact hnogen str hs (List.mem_append_right _ (by
            simp only [Stmt.modifiedVars, List.mem_append]
            exact Or.inl hm))
      have hnge : SrcNoGenWrites NondetElim.isGeneratedName ess := by
        intro str hs hm
        rcases List.mem_append.mp hm with hd | hm
        · exact hnogen str hs (List.mem_append_left _ (by
            simp only [Stmt.definedVars, Bool.false_eq_true, ite_false, List.mem_append]
            exact Or.inr hd))
        · exact hnogen str hs (List.mem_append_right _ (by
            simp only [Stmt.modifiedVars, List.mem_append]
            exact Or.inr hm))
      obtain ⟨ht, _⟩ := Block.nondetElimM_defUseWellFormed tss σ source target
        declaredSource declaredTarget hrel hwf hdecl hfvarops hdu.1.2 hngt
      let σ₁ := (Block.nondetElimM tss σ).2
      have hstep₁ : StringGenState.GenStep σ σ₁ := Block.nondetElimM_genStep tss σ
      obtain ⟨he, _⟩ := Block.nondetElimM_defUseWellFormed ess σ₁ source target
        declaredSource declaredTarget (NondetElimDefinedRel.mono hstep₁ hrel)
        (hstep₁.wf_mono hwf) hdecl hfvarops hdu.2 hnge
      refine ⟨?_, ?_⟩
      · rw [Stmt.nondetElimM_ite_det_out]
        simp only [Block.defUseWellFormed, Stmt.defUseWellFormed, Bool.and_eq_true,
          Bool.and_true]
        exact ⟨⟨⟨all_target_true hrel hdu.1.1.1,
          List.all_mono hdecl hdu.1.1.2⟩, ht⟩, he⟩
      · rw [Stmt.nondetElimM_ite_det_state, Stmt.nondetElimM_ite_det_out]
        simp only [Stmt.definedVars, Block.definedVars,
          ↓reduceIte, List.append_nil]
        have hsource : (fun x => source x || decide (x ∈ ([] : List P.Ident))) = source := by
          funext x
          simp
        have htarget : (fun x => target x || decide (x ∈ ([] : List P.Ident))) = target := by
          funext x
          simp
        rw [hsource, htarget]
        exact
          NondetElimDefinedRel.mono
            (StringGenState.GenStep.trans hstep₁
              (Block.nondetElimM_genStep ess σ₁)) hrel
  | .ite .nondet tss ess md =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      let g := (StringGenState.gen NondetElim.prefixIte σ).1
      let σ₁ := (StringGenState.gen NondetElim.prefixIte σ).2
      have hgkind : NondetElim.isGeneratedName g := NondetElim.isGeneratedName_gen.1 σ
      have hgfalse : target (HasIdent.ident (P := P) g) = false :=
        hrel.2.1 g hgkind (StringGenState.stringGens_gen_not_in _ _ hwf)
      let target₁ := fun x => target x || decide (x = HasIdent.ident (P := P) g)
      have hrel₁ : NondetElimDefinedRel σ₁ source target₁ :=
        NondetElimDefinedRel.add_guard hrel NondetElim.prefixIte hgkind
      have hstep₀ : StringGenState.GenStep σ σ₁ :=
        StringGenState.GenStep.of_gen NondetElim.prefixIte σ
      have hngt : SrcNoGenWrites NondetElim.isGeneratedName tss := by
        intro str hs hm
        rcases List.mem_append.mp hm with hd | hm
        · exact hnogen str hs (List.mem_append_left _ (by
            simp only [Stmt.definedVars, Bool.false_eq_true, ite_false, List.mem_append]
            exact Or.inl hd))
        · exact hnogen str hs (List.mem_append_right _ (by
            simp only [Stmt.modifiedVars, List.mem_append]
            exact Or.inl hm))
      have hnge : SrcNoGenWrites NondetElim.isGeneratedName ess := by
        intro str hs hm
        rcases List.mem_append.mp hm with hd | hm
        · exact hnogen str hs (List.mem_append_left _ (by
            simp only [Stmt.definedVars, Bool.false_eq_true, ite_false, List.mem_append]
            exact Or.inr hd))
        · exact hnogen str hs (List.mem_append_right _ (by
            simp only [Stmt.modifiedVars, List.mem_append]
            exact Or.inr hm))
      obtain ⟨ht, _⟩ := Block.nondetElimM_defUseWellFormed tss σ₁ source target₁
        declaredSource declaredTarget hrel₁ (hstep₀.wf_mono hwf) hdecl hfvarops hdu.1.2 hngt
      let σ₂ := (Block.nondetElimM tss σ₁).2
      have hstep₁ : StringGenState.GenStep σ₁ σ₂ := Block.nondetElimM_genStep tss σ₁
      obtain ⟨he, _⟩ := Block.nondetElimM_defUseWellFormed ess σ₂ source target₁
        declaredSource declaredTarget (NondetElimDefinedRel.mono hstep₁ hrel₁)
        (hstep₁.wf_mono (hstep₀.wf_mono hwf)) hdecl hfvarops hdu.2 hnge
      have hguard : (ExprOrNondet.det
          (HasFvar.mkTypedFvar (P := P) (HasIdent.ident (P := P) g) HasBool.boolTy)).getVars.all
          target₁ = true := by
        simp only [ExprOrNondet.getVars, List.all_eq_true]
        intro x hx
        have hx' := LawfulHasFvars.mkTypedFvar_getFvars
          (P := P) (HasIdent.ident (P := P) g) HasBool.boolTy hx
        simp only [List.mem_singleton] at hx'
        subst x
        simp [target₁]
      have hguardops : (ExprOrNondet.det
          (HasFvar.mkTypedFvar (P := P) (HasIdent.ident (P := P) g) HasBool.boolTy)).getOps.all
          declaredTarget = true := by
        simp only [ExprOrNondet.getOps, hfvarops]
        rfl
      have hinit : Stmt.defUseWellFormed target declaredTarget
          (.cmd (HasInit.init (P := P) (CmdT := Cmd P)
            (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) = true := by
        exact init_defUseWellFormed target declaredTarget
          (HasIdent.ident (P := P) g) HasBool.boolTy md hgfalse
      have hacc :
          (fun x => target x || decide
            (x ∈ Stmt.definedVars
              (.cmd (HasInit.init (P := P) (CmdT := Cmd P)
                (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) true)) =
          target₁ := by
        funext x
        rw [init_true_definedVars]
        change (target x || decide
          (x ∈ [HasIdent.ident (P := P) g])) =
          (target x || decide (x = HasIdent.ident (P := P) g))
        simp
      have hite : Stmt.defUseWellFormed target₁ declaredTarget
          (.ite (.det (HasFvar.mkTypedFvar (P := P)
            (HasIdent.ident (P := P) g) HasBool.boolTy))
            (Block.nondetElimM tss σ₁).1
            (Block.nondetElimM ess σ₂).1 md) = true := by
        simp only [Stmt.defUseWellFormed, Bool.and_eq_true]
        exact ⟨⟨⟨hguard, hguardops⟩, ht⟩, he⟩
      refine ⟨?_, ?_⟩
      · rw [Stmt.nondetElimM_ite_nondet_out]
        simp only [Block.defUseWellFormed, Bool.and_eq_true,
          Bool.and_true]
        rw [hacc]
        exact ⟨hinit, hite⟩
      · have hout : Block.definedVars
            (Stmt.nondetElimM (.ite .nondet tss ess md) σ).1 true =
            [HasIdent.ident (P := P) g] := by
          rw [Stmt.nondetElimM_ite_nondet_out]
          simp only [Block.definedVars, Stmt.definedVars,
            ↓reduceIte, List.append_nil]
          rw [init_cmd_definedVars]
        rw [Stmt.nondetElimM_ite_nondet_state, hout]
        simp only [Stmt.definedVars, ↓reduceIte]
        have hsource :
            (fun x => source x || decide (x ∈ ([] : List P.Ident))) = source := by
          funext x
          simp
        have htarget :
            (fun x => target x || decide
              (x ∈ [HasIdent.ident (P := P) g])) = target₁ := by
          funext x
          simp [target₁]
        rw [hsource, htarget]
        exact NondetElimDefinedRel.mono
            (StringGenState.GenStep.trans hstep₁
              (Block.nondetElimM_genStep ess σ₂)) hrel₁
  | .loop (.det e) m inv body md =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      have hng : SrcNoGenWrites NondetElim.isGeneratedName body := by
        intro str hs hm
        exact hnogen str hs (by simpa [Stmt.definedVars, Stmt.modifiedVars] using hm)
      obtain ⟨hb, _⟩ := Block.nondetElimM_defUseWellFormed body σ source target
        declaredSource declaredTarget hrel hwf hdecl hfvarops hdu.2 hng
      refine ⟨?_, ?_⟩
      · rw [Stmt.nondetElimM_loop_det_out]
        simp only [Block.defUseWellFormed, Stmt.defUseWellFormed, Bool.and_eq_true,
          Bool.and_true]
        exact ⟨⟨⟨⟨⟨⟨all_target_true hrel hdu.1.1.1.1.1.1,
          List.all_mono hdecl hdu.1.1.1.1.1.2⟩,
          all_target_true hrel hdu.1.1.1.1.2⟩,
          List.all_mono hdecl hdu.1.1.1.2⟩,
          all_target_true hrel hdu.1.1.2⟩,
          List.all_mono hdecl hdu.1.2⟩,
          hb⟩
      · rw [Stmt.nondetElimM_loop_det_state, Stmt.nondetElimM_loop_det_out]
        simp only [Stmt.definedVars, Block.definedVars,
          ↓reduceIte, List.append_nil]
        have hsource : (fun x => source x || decide (x ∈ ([] : List P.Ident))) = source := by
          funext x
          simp
        have htarget : (fun x => target x || decide (x ∈ ([] : List P.Ident))) = target := by
          funext x
          simp
        rw [hsource, htarget]
        exact
          NondetElimDefinedRel.mono (Block.nondetElimM_genStep body σ) hrel
  | .loop .nondet m inv body md =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      let g := (StringGenState.gen NondetElim.prefixLoop σ).1
      let σ₁ := (StringGenState.gen NondetElim.prefixLoop σ).2
      have hgkind : NondetElim.isGeneratedName g := NondetElim.isGeneratedName_gen.2 σ
      have hgfalse : target (HasIdent.ident (P := P) g) = false :=
        hrel.2.1 g hgkind (StringGenState.stringGens_gen_not_in _ _ hwf)
      let target₁ := fun x => target x || decide (x = HasIdent.ident (P := P) g)
      have hrel₁ : NondetElimDefinedRel σ₁ source target₁ :=
        NondetElimDefinedRel.add_guard hrel NondetElim.prefixLoop hgkind
      have hstep₀ : StringGenState.GenStep σ σ₁ :=
        StringGenState.GenStep.of_gen NondetElim.prefixLoop σ
      have hng : SrcNoGenWrites NondetElim.isGeneratedName body := by
        intro str hs hm
        exact hnogen str hs (by simpa [Stmt.definedVars, Stmt.modifiedVars] using hm)
      obtain ⟨hb, hrelb⟩ := Block.nondetElimM_defUseWellFormed body σ₁ source target₁
        declaredSource declaredTarget hrel₁ (hstep₀.wf_mono hwf) hdecl hfvarops
        hdu.2 hng
      have hguard : (ExprOrNondet.det
          (HasFvar.mkTypedFvar (P := P) (HasIdent.ident (P := P) g) HasBool.boolTy)).getVars.all
          target₁ = true := by
        simp only [ExprOrNondet.getVars, List.all_eq_true]
        intro x hx
        have hx' := LawfulHasFvars.mkTypedFvar_getFvars
          (P := P) (HasIdent.ident (P := P) g) HasBool.boolTy hx
        simp only [List.mem_singleton] at hx'
        subst x
        simp [target₁]
      have hgbody : (fun x => target₁ x || decide
          (x ∈ Block.definedVars (Block.nondetElimM body σ₁).1 true))
          (HasIdent.ident (P := P) g) = true := by
        simp [target₁]
      have hguardops : (ExprOrNondet.det
          (HasFvar.mkTypedFvar (P := P) (HasIdent.ident (P := P) g) HasBool.boolTy)).getOps.all
          declaredTarget = true := by
        simp only [ExprOrNondet.getOps, hfvarops]
        rfl
      have hinit : Stmt.defUseWellFormed target declaredTarget
          (.cmd (HasInit.init (P := P) (CmdT := Cmd P)
            (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) = true := by
        exact init_defUseWellFormed target declaredTarget
          (HasIdent.ident (P := P) g) HasBool.boolTy md hgfalse
      have hacc :
          (fun x => target x || decide
            (x ∈ Stmt.definedVars
              (.cmd (HasInit.init (P := P) (CmdT := Cmd P)
                (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) true)) =
          target₁ := by
        funext x
        rw [init_true_definedVars]
        change (target x || decide
          (x ∈ [HasIdent.ident (P := P) g])) =
          (target x || decide (x = HasIdent.ident (P := P) g))
        simp
      have hhavoc : Stmt.defUseWellFormed
          (fun x => target₁ x || decide
            (x ∈ Block.definedVars (Block.nondetElimM body σ₁).1 true))
          declaredTarget
          (.cmd (HasHavoc.havoc (P := P) (CmdT := Cmd P)
            (HasIdent.ident (P := P) g) md)) = true := by
        rw [havoc_defUseWellFormed]
        exact hgbody
      have hbody : Block.defUseWellFormed target₁ declaredTarget
          ((Block.nondetElimM body σ₁).1 ++
            [.cmd (HasHavoc.havoc (P := P) (CmdT := Cmd P)
              (HasIdent.ident (P := P) g) md)]) = true := by
        rw [Block.defUseWellFormed_append]
        simp only [Bool.and_eq_true]
        refine ⟨hb, ?_⟩
        simpa [Block.defUseWellFormed] using hhavoc
      have hloop : Stmt.defUseWellFormed target₁ declaredTarget
          (.loop (.det (HasFvar.mkTypedFvar (P := P)
            (HasIdent.ident (P := P) g) HasBool.boolTy)) m inv
            ((Block.nondetElimM body σ₁).1 ++
              [.cmd (HasHavoc.havoc (P := P) (CmdT := Cmd P)
                (HasIdent.ident (P := P) g) md)]) md) = true := by
        simp only [Stmt.defUseWellFormed, Bool.and_eq_true]
        exact ⟨⟨⟨⟨⟨⟨hguard, hguardops⟩,
          all_target_true hrel₁ hdu.1.1.1.1.2⟩,
          List.all_mono hdecl hdu.1.1.1.2⟩,
          all_target_true hrel₁ hdu.1.1.2⟩,
          List.all_mono hdecl hdu.1.2⟩,
          hbody⟩
      refine ⟨?_, ?_⟩
      · rw [Stmt.nondetElimM_loop_nondet_out]
        simp only [Block.defUseWellFormed, Bool.and_eq_true,
          Bool.and_true]
        rw [hacc]
        exact ⟨hinit, hloop⟩
      · have hout : Block.definedVars
            (Stmt.nondetElimM (.loop .nondet m inv body md) σ).1 true =
            [HasIdent.ident (P := P) g] := by
          rw [Stmt.nondetElimM_loop_nondet_out]
          simp only [Block.definedVars, Stmt.definedVars,
            ↓reduceIte, List.append_nil]
          rw [init_cmd_definedVars]
        rw [Stmt.nondetElimM_loop_nondet_state, hout]
        simp only [Stmt.definedVars, ↓reduceIte]
        have hsource :
            (fun x => source x || decide (x ∈ ([] : List P.Ident))) = source := by
          funext x
          simp
        have htarget :
            (fun x => target x || decide
              (x ∈ [HasIdent.ident (P := P) g])) = target₁ := by
          funext x
          simp [target₁]
        rw [hsource, htarget]
        exact NondetElimDefinedRel.mono
          (Block.nondetElimM_genStep body σ₁) hrel₁
  | .exit lbl md =>
      exact ⟨by simp [Stmt.nondetElimM, Block.defUseWellFormed,
        Stmt.defUseWellFormed], by simpa [Stmt.nondetElimM,
        Stmt.definedVars, Block.definedVars] using hrel⟩
  | .typeDecl t md =>
      exact ⟨by simp [Stmt.nondetElimM, Block.defUseWellFormed,
        Stmt.defUseWellFormed], by simpa [Stmt.nondetElimM,
        Stmt.definedVars, Block.definedVars] using hrel⟩
  termination_by sizeOf s

/-- Block-level counterpart: the pass preserves def-use well-formedness of a
block and extends the defined-register relation by the block's newly defined
variables. -/
theorem Block.nondetElimM_defUseWellFormed {P : PureExpr}
    [HasIdent P] [LawfulHasIdent P] [DecidableEq P.Ident]
    [HasFvar P] [HasFvars P] [LawfulHasFvars P]
    [HasBool P] [HasOps P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (source target declaredSource declaredTarget : P.Ident → Bool)
    (hrel : NondetElimDefinedRel σ source target)
    (hwf : StringGenState.WF σ)
    (hdecl : ∀ x, declaredSource x = true → declaredTarget x = true)
    (hfvarops : ∀ x, HasOps.getOps
      (HasFvar.mkTypedFvar (P := P) x HasBool.boolTy) = [])
    (hdu : Block.defUseWellFormed source declaredSource ss = true)
    (hnogen : SrcNoGenWrites NondetElim.isGeneratedName ss) :
    Block.defUseWellFormed target declaredTarget (Block.nondetElimM ss σ).1 = true ∧
    NondetElimDefinedRel (Block.nondetElimM ss σ).2
      (fun x => source x || decide (x ∈ Block.definedVars ss true))
      (fun x => target x || decide
        (x ∈ Block.definedVars (Block.nondetElimM ss σ).1 true)) := by
  match ss with
  | [] =>
      exact ⟨by simp [Block.nondetElimM, Block.defUseWellFormed],
        by simpa [Block.nondetElimM, Block.definedVars] using hrel⟩
  | s :: rest =>
      simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
      have hngs : ∀ str, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉
            (Stmt.definedVars s false ++ Stmt.modifiedVars s) := by
        intro str hs hm
        apply hnogen str hs
        rw [Block.definedVars, Block.modifiedVars]
        rcases List.mem_append.mp hm with hd | hm
        · exact List.mem_append_left _ (List.mem_append_left _ hd)
        · exact List.mem_append_right _ (List.mem_append_left _ hm)
      have hngr : SrcNoGenWrites NondetElim.isGeneratedName rest := by
        intro str hs hm
        apply hnogen str hs
        rw [Block.definedVars, Block.modifiedVars]
        rcases List.mem_append.mp hm with hd | hm
        · exact List.mem_append_left _ (List.mem_append_right _ hd)
        · exact List.mem_append_right _ (List.mem_append_right _ hm)
      obtain ⟨hs, hrels⟩ := Stmt.nondetElimM_defUseWellFormed s σ source target
        declaredSource declaredTarget hrel hwf hdecl hfvarops hdu.1 hngs
      let σ₁ := (Stmt.nondetElimM s σ).2
      let source₁ := fun x => source x || decide (x ∈ Stmt.definedVars s true)
      let target₁ := fun x => target x || decide
        (x ∈ Block.definedVars (Stmt.nondetElimM s σ).1 true)
      obtain ⟨hr, hrelr⟩ := Block.nondetElimM_defUseWellFormed rest σ₁ source₁ target₁
        declaredSource declaredTarget hrels
        ((Stmt.nondetElimM_genStep s σ).wf_mono hwf) hdecl hfvarops hdu.2 hngr
      refine ⟨?_, ?_⟩
      · rw [Block.nondetElimM_cons_out, Block.defUseWellFormed_append]
        simpa only [Bool.and_eq_true] using And.intro hs hr
      · rw [Block.nondetElimM_cons_state, Block.nondetElimM_cons_out,
          Block.definedVars_append, Block.definedVars]
        have hsource :
            (fun x => source x || decide
              (x ∈ Stmt.definedVars s true ++ Block.definedVars rest true)) =
            (fun x => source x || decide (x ∈ Stmt.definedVars s true) ||
              decide (x ∈ Block.definedVars rest true)) := by
          funext x
          by_cases hsx : x ∈ Stmt.definedVars s true <;>
            by_cases hrx : x ∈ Block.definedVars rest true <;>
            simp [hsx, hrx]
        have htarget :
            (fun x => target x || decide
              (x ∈ Block.definedVars (Stmt.nondetElimM s σ).1 true ++
                Block.definedVars (Block.nondetElimM rest σ₁).1 true)) =
            (fun x => target x ||
              decide (x ∈ Block.definedVars (Stmt.nondetElimM s σ).1 true) ||
              decide (x ∈ Block.definedVars
                (Block.nondetElimM rest σ₁).1 true)) := by
          funext x
          by_cases hsx : x ∈ Block.definedVars (Stmt.nondetElimM s σ).1 true <;>
            by_cases hrx : x ∈ Block.definedVars
              (Block.nondetElimM rest σ₁).1 true <;>
            simp [hsx, hrx]
        rw [hsource, htarget]
        simpa [source₁, target₁, Bool.or_assoc] using hrelr
  termination_by sizeOf ss

end

/-- Top-level: `Block.nondetElim` preserves def-use well-formedness of a block
whose source never defines a generated guard name. -/
theorem Block.nondetElim_defUseWellFormed {P : PureExpr}
    [HasIdent P] [LawfulHasIdent P] [DecidableEq P.Ident]
    [HasFvar P] [HasFvars P] [LawfulHasFvars P]
    [HasBool P] [HasOps P]
    (ss : List (Stmt P (Cmd P)))
    (defined declaredSource declaredTarget : P.Ident → Bool)
    (hkind : ∀ s, NondetElim.isGeneratedName s →
      defined (HasIdent.ident (P := P) s) = false)
    (hdecl : ∀ x, declaredSource x = true → declaredTarget x = true)
    (hfvarops : ∀ x, HasOps.getOps
      (HasFvar.mkTypedFvar (P := P) x HasBool.boolTy) = [])
    (hdu : Block.defUseWellFormed defined declaredSource ss = true)
    (hnogen : SrcNoGenWrites NondetElim.isGeneratedName ss) :
    Block.defUseWellFormed defined declaredTarget (Block.nondetElim ss) = true := by
  have hrel : NondetElimDefinedRel StringGenState.emp defined defined := by
    refine ⟨hkind, ?_, ?_⟩
    · intro s hs _
      exact hkind s hs
    · intro x _
      rfl
  exact (Block.nondetElimM_defUseWellFormed ss StringGenState.emp
    defined defined declaredSource declaredTarget hrel StringGenState.wf_emp
    hdecl hfvarops hdu hnogen).1

end Imperative

end -- public section

namespace Core

open Imperative

/-! ## Core nondeterminism elimination

The pass passes `.cmd c` through unchanged and only ever fabricates `init`/`havoc`
commands, none of which is a `call`; hence `noCalls` is preserved. -/

mutual
/-- Running the generic nondet-elimination pass on a call-free Core statement
leaves it call-free: if every substatement of `s` is a non-call, so is every
substatement of the rewritten statement. The pass passes `.cmd` through unchanged
and only fabricates `init`/`havoc` commands, none of which is a procedure `call`. -/
theorem Stmt.nondetElimM_isNotCall (s : Statement) (σ : StringGenState)
    (h : Imperative.Stmt.allSubstmts Statement.isNotCall s = true) :
    Imperative.Block.allSubstmts Statement.isNotCall
      (Imperative.Stmt.nondetElimM s σ).1 = true := by
  match s with
  | .cmd c =>
      simpa only [Imperative.Stmt.nondetElimM, Imperative.Block.allSubstmts,
                  Imperative.Stmt.allSubstmts, Bool.and_true] using h
  | .block lbl bss md =>
      rw [Imperative.Stmt.nondetElimM_block_out]
      simp only [Imperative.Block.allSubstmts, Imperative.Stmt.allSubstmts,
                 Statement.isNotCall, Bool.true_and, Bool.and_true]
      simp only [Imperative.Stmt.allSubstmts, Statement.isNotCall, Bool.true_and] at h
      exact Block.nondetElimM_isNotCall bss σ h
  | .ite (.det e) tss ess md =>
      rw [Imperative.Stmt.nondetElimM_ite_det_out]
      simp only [Imperative.Block.allSubstmts, Imperative.Stmt.allSubstmts,
                 Statement.isNotCall, Bool.true_and, Bool.and_true]
      simp only [Imperative.Stmt.allSubstmts, Statement.isNotCall, Bool.true_and,
                 Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨Block.nondetElimM_isNotCall tss σ h.1,
                                  Block.nondetElimM_isNotCall ess _ h.2⟩
  | .ite .nondet tss ess md =>
      rw [Imperative.Stmt.nondetElimM_ite_nondet_out]
      simp only [Imperative.Block.allSubstmts, Imperative.Stmt.allSubstmts,
                 CmdExt.hasInit_eq, Statement.isNotCall, Bool.true_and, Bool.and_true]
      simp only [Imperative.Stmt.allSubstmts, Statement.isNotCall, Bool.true_and,
                 Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨Block.nondetElimM_isNotCall tss _ h.1,
                                  Block.nondetElimM_isNotCall ess _ h.2⟩
  | .loop (.det e) m inv body md =>
      rw [Imperative.Stmt.nondetElimM_loop_det_out]
      simp only [Imperative.Block.allSubstmts, Imperative.Stmt.allSubstmts,
                 Statement.isNotCall, Bool.true_and, Bool.and_true]
      simp only [Imperative.Stmt.allSubstmts, Statement.isNotCall, Bool.true_and] at h
      exact Block.nondetElimM_isNotCall body σ h
  | .loop .nondet m inv body md =>
      rw [Imperative.Stmt.nondetElimM_loop_nondet_out]
      simp only [Imperative.Block.allSubstmts, Imperative.Stmt.allSubstmts,
                 Imperative.Block.allSubstmts_append, CmdExt.hasInit_eq, CmdExt.hasHavoc_eq,
                 Statement.isNotCall, Bool.true_and, Bool.and_true]
      simp only [Imperative.Stmt.allSubstmts, Statement.isNotCall, Bool.true_and] at h
      exact Block.nondetElimM_isNotCall body _ h
  | .exit lbl md =>
      simp [Imperative.Stmt.nondetElimM, Imperative.Block.allSubstmts,
            Imperative.Stmt.allSubstmts, Statement.isNotCall]
  | .typeDecl t md =>
      simp [Imperative.Stmt.nondetElimM, Imperative.Block.allSubstmts,
            Imperative.Stmt.allSubstmts, Statement.isNotCall]
  termination_by sizeOf s

/-- Statement-list counterpart of `Stmt.nondetElimM_isNotCall`: running the
generic nondet-elimination pass on a call-free Core statement list leaves it
call-free. -/
theorem Block.nondetElimM_isNotCall (ss : Statements) (σ : StringGenState)
    (h : Imperative.Block.allSubstmts Statement.isNotCall ss = true) :
    Imperative.Block.allSubstmts Statement.isNotCall
      (Imperative.Block.nondetElimM ss σ).1 = true := by
  match ss with
  | [] => simp [Imperative.Block.nondetElimM, Imperative.Block.allSubstmts]
  | s :: rest =>
      rw [Imperative.Block.nondetElimM_cons_out, Imperative.Block.allSubstmts_append]
      simp only [Imperative.Block.allSubstmts, Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨Stmt.nondetElimM_isNotCall s σ h.1,
                                  Block.nondetElimM_isNotCall rest _ h.2⟩
  termination_by sizeOf ss
end

/-! ## `nondetElim` commutes with the embedding -/

mutual
/-- Nondet-elimination commutes with the embedding on a statement: running the
pass on an embedded base statement equals embedding the base pass's output, with
the fresh-name generator state threaded identically on both sides. -/
theorem embedStmt_nondetElimM
    (b : Imperative.Stmt Expression (Cmd Expression)) (σ : StringGenState) :
    Stmt.nondetElimM (embedStmt b) σ
      = (embedStmts (Stmt.nondetElimM b σ).1, (Stmt.nondetElimM b σ).2) := by
  match b with
  | .cmd c => simp [embedStmt, Stmt.nondetElimM, embedStmts]
  | .block lbl bss md =>
      simp only [embedStmt, Stmt.nondetElimM, embedStmts_nondetElimM bss σ]
      rcases Block.nondetElimM bss σ with ⟨bss', σ'⟩
      simp [embedStmts, embedStmt]
  | .ite (.det e) tss ess md =>
      simp only [embedStmt, Stmt.nondetElimM, embedStmts_nondetElimM tss σ,
        embedStmts_nondetElimM ess _]
      split <;> split <;> simp_all [embedStmts, embedStmt]
  | .ite .nondet tss ess md =>
      simp only [embedStmt, Stmt.nondetElimM, embedStmts_nondetElimM tss _,
        embedStmts_nondetElimM ess _]
      split <;> split <;> simp_all [embedStmts, embedStmt, CmdExt.hasInit_eq]
  | .loop (.det e) m inv body md =>
      simp only [embedStmt, Stmt.nondetElimM, embedStmts_nondetElimM body σ]
      rcases Block.nondetElimM body σ with ⟨body', σ'⟩
      simp [embedStmts, embedStmt]
  | .loop .nondet m inv body md =>
      simp only [embedStmt, Stmt.nondetElimM, embedStmts_nondetElimM body _]
      rcases Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2 with ⟨body', σ₂⟩
      simp [embedStmts, embedStmt, embedStmts_append,
        CmdExt.hasInit_eq, CmdExt.hasHavoc_eq]
  | .exit lbl md => simp [embedStmt, Stmt.nondetElimM, embedStmts]
  | .typeDecl t md => simp [embedStmt, Stmt.nondetElimM, embedStmts]
  termination_by sizeOf b

/-- Statement-list counterpart of `embedStmt_nondetElimM`: running
nondet-elimination on an embedded base statement list equals embedding the base
pass's output, threading the fresh-name generator state identically. -/
theorem embedStmts_nondetElimM
    (bs : List (Imperative.Stmt Expression (Cmd Expression)))
    (σ : StringGenState) :
    Block.nondetElimM (embedStmts bs) σ
      = (embedStmts (Block.nondetElimM bs σ).1, (Block.nondetElimM bs σ).2) := by
  match bs with
  | [] => simp [embedStmts, Block.nondetElimM]
  | s :: rest =>
      simp only [embedStmts, Block.nondetElimM, embedStmt_nondetElimM s σ,
        embedStmts_nondetElimM rest _]
      split <;> split <;> simp_all [embedStmts_append]
  termination_by sizeOf bs
end

/-- `Block.nondetElim` commutes with the embedding: running it on an embedded
base block equals embedding its base output. -/
theorem embedStmts_nondetElim (bs : List (Imperative.Stmt Expression (Cmd Expression))) :
    Imperative.Block.nondetElim (embedStmts bs)
      = embedStmts (Imperative.Block.nondetElim bs) := by
  simp only [Imperative.Block.nondetElim]
  rw [embedStmts_nondetElimM bs StringGenState.emp]

end Core

end -- public section
