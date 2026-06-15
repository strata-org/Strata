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

/-! # `nondetElim` — structured-to-structured nondeterministic-control elimination

Replaces every nondeterministic `.ite`/`.loop` guard with a deterministic read
of a freshly-generated boolean variable that is havoc'd at the construct's site.
After the pass, no `.ite`/`.loop` carries a `.nondet` guard; nondeterminism
survives only as havoc commands. See
`docs/superpowers/specs/2026-06-11-nondet-elim-pass-design.md`.

The fresh-name prefixes are distinct from the str2unstr translator's
`$__nondet_*` prefixes so the two passes' generated names are unmistakable in
origin; disjointness in the proofs is suffix-based, not prefix-based. -/

/-- Fresh-name prefix for nondet `.ite` guard variables. -/
@[expose] def ndelimItePrefix : String := "$__ndelim_ite$"

/-- Fresh-name prefix for nondet `.loop` guard variables. -/
@[expose] def ndelimLoopPrefix : String := "$__ndelim_loop$"

mutual
/-- Rewrite a single statement, eliminating nondeterministic control. Threads a
`StringGenState`. For `.ite .nondet`, allocates a fresh boolean `$g`, emits a
local `init $g := *` before the rewritten ite, and makes the guard `.det $g`.
For `.loop .nondet`, emits a before-loop `init $g := *`, makes the guard
`.det $g`, and appends a body-tail `set $g := *` (re-havoc each iteration). Det
constructs and atomic commands pass through, recursing into sub-bodies. -/
@[expose] def Stmt.nondetElimM {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) : StringGenM (List (Stmt P (Cmd P))) :=
  match s with
  | .cmd c => fun σ => ([.cmd c], σ)
  | .block lbl bss md => fun σ =>
      let (bss', σ') := Block.nondetElimM bss σ
      ([.block lbl bss' md], σ')
  | .ite (.det e) tss ess md => fun σ =>
      let (tss', σ₁) := Block.nondetElimM tss σ
      let (ess', σ₂) := Block.nondetElimM ess σ₁
      ([.ite (.det e) tss' ess' md], σ₂)
  | .ite .nondet tss ess md => fun σ =>
      let (g, σ₁) := StringGenState.gen ndelimItePrefix σ
      let ident := HasIdent.ident (P := P) g
      let (tss', σ₂) := Block.nondetElimM tss σ₁
      let (ess', σ₃) := Block.nondetElimM ess σ₂
      ([.cmd (HasInit.init ident HasBool.boolTy .nondet md),
        .ite (.det (HasFvar.mkFvar ident)) tss' ess' md], σ₃)
  | .loop (.det e) m inv body md => fun σ =>
      let (body', σ') := Block.nondetElimM body σ
      ([.loop (.det e) m inv body' md], σ')
  | .loop .nondet m inv body md => fun σ =>
      let (g, σ₁) := StringGenState.gen ndelimLoopPrefix σ
      let ident := HasIdent.ident (P := P) g
      let (body', σ₂) := Block.nondetElimM body σ₁
      ([.cmd (HasInit.init ident HasBool.boolTy .nondet md),
        .loop (.det (HasFvar.mkFvar ident)) m inv
          (body' ++ [.cmd (HasHavoc.havoc ident md)]) md], σ₂)
  | .exit lbl md => fun σ => ([.exit lbl md], σ)
  | .funcDecl d md => fun σ => ([.funcDecl d md], σ)
  | .typeDecl t md => fun σ => ([.typeDecl t md], σ)
  termination_by sizeOf s

/-- Apply `Stmt.nondetElimM` to each statement of the block, threading the state
and concatenating the resulting lists. -/
@[expose] def Block.nondetElimM {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) : StringGenM (List (Stmt P (Cmd P))) :=
  match ss with
  | [] => fun σ => ([], σ)
  | s :: rest => fun σ =>
      let (ss_s, σ₁) := Stmt.nondetElimM s σ
      let (ss_r, σ₂) := Block.nondetElimM rest σ₁
      (ss_s ++ ss_r, σ₂)
  termination_by sizeOf ss
end

section Projections

theorem Stmt.nondetElimM_block_out {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.block lbl bss md) σ).1 =
      [Stmt.block lbl (Block.nondetElimM bss σ).1 md] := by
  rw [Stmt.nondetElimM]
  rcases h : Block.nondetElimM bss σ with ⟨bss', σ'⟩
  simp only [h]

theorem Stmt.nondetElimM_ite_det_out {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (e : P.Expr) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite (.det e) tss ess md) σ).1 =
      [Stmt.ite (.det e) (Block.nondetElimM tss σ).1
        (Block.nondetElimM ess (Block.nondetElimM tss σ).2).1 md] := by
  rw [Stmt.nondetElimM]
  rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
  rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
  simp only [h₁, h₂]

theorem Stmt.nondetElimM_ite_nondet_out {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (tss ess : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite .nondet tss ess md) σ).1 =
      let g := (StringGenState.gen ndelimItePrefix σ).1
      let ident := HasIdent.ident (P := P) g
      let σ₁ := (StringGenState.gen ndelimItePrefix σ).2
      [Stmt.cmd (HasInit.init ident HasBool.boolTy .nondet md),
       Stmt.ite (.det (HasFvar.mkFvar ident)) (Block.nondetElimM tss σ₁).1
         (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md] := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen ndelimItePrefix σ with ⟨g, σ₁⟩
  rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
  rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
  simp only [hg, h₁, h₂]

theorem Stmt.nondetElimM_loop_det_out {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (e : P.Expr) (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop (.det e) m inv body md) σ).1 =
      [Stmt.loop (.det e) m inv (Block.nondetElimM body σ).1 md] := by
  rw [Stmt.nondetElimM]
  rcases h : Block.nondetElimM body σ with ⟨body', σ'⟩
  simp only [h]

theorem Stmt.nondetElimM_loop_nondet_out {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop .nondet m inv body md) σ).1 =
      let g := (StringGenState.gen ndelimLoopPrefix σ).1
      let ident := HasIdent.ident (P := P) g
      let σ₁ := (StringGenState.gen ndelimLoopPrefix σ).2
      [Stmt.cmd (HasInit.init ident HasBool.boolTy .nondet md),
       Stmt.loop (.det (HasFvar.mkFvar ident)) m inv
         ((Block.nondetElimM body σ₁).1 ++ [Stmt.cmd (HasHavoc.havoc ident md)]) md] := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen ndelimLoopPrefix σ with ⟨g, σ₁⟩
  rcases h : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
  simp only [hg, h]

theorem Block.nondetElimM_cons_out {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.nondetElimM (s :: rest) σ).1 =
      (Stmt.nondetElimM s σ).1 ++
        (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).1 := by
  rw [Block.nondetElimM]
  rcases h₁ : Stmt.nondetElimM s σ with ⟨ss_s, σ₁⟩
  rcases h₂ : Block.nondetElimM rest σ₁ with ⟨ss_r, σ₂⟩
  simp only [h₁, h₂]

end Projections

/-- Pure top-level wrapper: run the monadic pass from the empty `StringGenState`
and discard the final state. -/
@[expose] def Block.nondetElim {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) : List (Stmt P (Cmd P)) :=
  (Block.nondetElimM ss StringGenState.emp).1

section Preservation

/-- `Block.loopHasNoInvariants` distributes over `++`. -/
theorem Block.loopHasNoInvariants_append {P : PureExpr} (xs ys : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (xs ++ ys) =
      (Block.loopHasNoInvariants xs && Block.loopHasNoInvariants ys) := by
  induction xs with
  | nil => simp [Block.loopHasNoInvariants]
  | cons x rest ih => simp [Block.loopHasNoInvariants, ih, Bool.and_assoc]

/-- `Block.noMeasureLoops` distributes over `++`. -/
theorem Block.noMeasureLoops_append {P : PureExpr} (xs ys : List (Stmt P (Cmd P))) :
    Block.noMeasureLoops (xs ++ ys) =
      (Block.noMeasureLoops xs && Block.noMeasureLoops ys) := by
  induction xs with
  | nil => simp [Block.noMeasureLoops]
  | cons x rest ih => simp [Block.noMeasureLoops, ih, Bool.and_assoc]

/-- `Block.noFuncDecl` distributes over `++`. -/
theorem Block.noFuncDecl_append {P : PureExpr} (xs ys : List (Stmt P (Cmd P))) :
    Block.noFuncDecl (xs ++ ys) =
      (Block.noFuncDecl xs && Block.noFuncDecl ys) := by
  induction xs with
  | nil => simp [Block.noFuncDecl]
  | cons x rest ih => simp [Block.noFuncDecl, ih, Bool.and_assoc]

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
  | .funcDecl d md => simp [Stmt.nondetElimM, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
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
  | .funcDecl d md => simp [Stmt.nondetElimM, Block.noMeasureLoops, Stmt.noMeasureLoops]
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

mutual
/-- `Stmt.nondetElimM` preserves `noFuncDecl`: the rewrite never emits a
function declaration and passes `.funcDecl` through unchanged (so under the
hypothesis the `.funcDecl` arm is vacuous). -/
theorem Stmt.nondetElimM_noFuncDecl {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.noFuncDecl s = true) :
    Block.noFuncDecl (Stmt.nondetElimM s σ).1 = true := by
  match s with
  | .cmd c => simp [Stmt.nondetElimM, Block.noFuncDecl, Stmt.noFuncDecl]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
      rw [Stmt.noFuncDecl] at h
      exact Block.nondetElimM_noFuncDecl bss σ h
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      rw [Stmt.noFuncDecl, Bool.and_eq_true] at h
      simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true,
                 Block.nondetElimM_noFuncDecl tss σ h.1,
                 Block.nondetElimM_noFuncDecl ess _ h.2]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      rw [Stmt.noFuncDecl, Bool.and_eq_true] at h
      simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true,
                 Block.nondetElimM_noFuncDecl tss _ h.1,
                 Block.nondetElimM_noFuncDecl ess _ h.2]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
      rw [Stmt.noFuncDecl] at h
      exact Block.nondetElimM_noFuncDecl body σ h
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      rw [Stmt.noFuncDecl] at h
      simp only [Block.noFuncDecl_append, Block.noFuncDecl,
                 Stmt.noFuncDecl, Bool.and_true,
                 Block.nondetElimM_noFuncDecl body _ h]
  | .exit lbl md => simp [Stmt.nondetElimM, Block.noFuncDecl, Stmt.noFuncDecl]
  | .funcDecl d md => exact absurd h (by simp [Stmt.noFuncDecl])
  | .typeDecl t md => simp [Stmt.nondetElimM, Block.noFuncDecl, Stmt.noFuncDecl]
  termination_by sizeOf s

theorem Block.nondetElimM_noFuncDecl {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.noFuncDecl ss = true) :
    Block.noFuncDecl (Block.nondetElimM ss σ).1 = true := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.noFuncDecl]
  | s :: rest =>
      rw [Block.noFuncDecl, Bool.and_eq_true] at h
      rw [Block.nondetElimM_cons_out, Block.noFuncDecl_append]
      simp only [Stmt.nondetElimM_noFuncDecl s σ h.1,
                 Block.nondetElimM_noFuncDecl rest _ h.2, Bool.and_true]
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

/-- Top-level preservation: `Block.nondetElim` preserves `noFuncDecl`. -/
theorem nondetElim_noFuncDecl {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (h : Block.noFuncDecl ss = true) :
    Block.noFuncDecl (Block.nondetElim ss) = true :=
  Block.nondetElimM_noFuncDecl ss StringGenState.emp h

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
      rcases hg : StringGenState.gen ndelimItePrefix σ with ⟨g, σ₁⟩
      rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
      rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
      simp only [hg, h₁, h₂]
      have g₀ : StringGenState.GenStep σ σ₁ := by
        have := StringGenState.GenStep.of_gen ndelimItePrefix σ; rw [hg] at this; exact this
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
      rcases hg : StringGenState.gen ndelimLoopPrefix σ with ⟨g, σ₁⟩
      rcases h : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
      simp only [hg, h]
      have g₀ : StringGenState.GenStep σ σ₁ := by
        have := StringGenState.GenStep.of_gen ndelimLoopPrefix σ; rw [hg] at this; exact this
      have g₁ := Block.nondetElimM_genStep body σ₁
      rw [h] at g₁
      exact StringGenState.GenStep.trans g₀ g₁
  | .exit lbl md => simp only [Stmt.nondetElimM]; exact StringGenState.GenStep.refl _
  | .funcDecl d md => simp only [Stmt.nondetElimM]; exact StringGenState.GenStep.refl _
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
