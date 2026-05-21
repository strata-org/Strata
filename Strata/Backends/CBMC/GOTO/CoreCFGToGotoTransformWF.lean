/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! # Discharging `WellFormedTranslation` against `coreCFGToGotoTransform`

This module is the start of Gap A in
`docs/CoreToGOTO_CorrectnessAnalysis.md`: prove that the program output
by `Strata.coreCFGToGotoTransform` (composed with `procedureToGotoCtxViaCFG`)
satisfies the `WellFormedTranslation` predicate consumed by
`CProverGOTO.coreCFGToGoto_forward_simulation`.

## What's here

This file isolates the **mechanical sub-lemmas** that any full discharge
will need, plus a small number of layout invariants that follow directly
from `Cmd.toGotoInstructions`'s shape:

1. **Per-`Cmd` shape lemmas** (`Cmd_toGotoInstructions_*_ok`): for each
   constructor of `Imperative.Cmd Core.Expression` (in the admitted
   fragment), if `Cmd.toGotoInstructions` succeeds, the resulting
   `GotoTransform` has a precisely-described `instructions` array
   appended and `nextLoc` advanced by exactly the count predicted by
   `Imperative.Cmd.gotoInstrCount`.

2. **Emit-helper shape lemmas** (`emitLabel_shape`, `emitCondGoto_shape`,
   `emitUncondGoto_shape`): each one-line, characterising the suffix
   each helper appends.

3. **`patchGotoTargets` invariants**: the second pass changes only the
   `target` field of selected instructions, so all type/guard/code
   /locationNum invariants above transfer through patching unchanged.

## What's not here

The full `coreCFGToGotoTransform_wellFormed` theorem requires an
**inductive invariant over the imperative `for`-loop** in the translator,
relating the partial-translation state after `k` blocks to a *partial*
`WellFormedTranslation` over `cfg.blocks.take k`. That invariant — and
the patching-correctness arguments tying `pendingPatches` to the final
`labelMap` — is the next, larger step. See
`docs/_workers/A_gap_a_report.md` for the concrete plan.

To keep `lake build` green at every commit we deliberately do **not**
state the top-level theorem in this module; it would either need a
`sorry` (forbidden) or a 500+-line proof we don't have. The sub-lemmas
below stand alone and remain useful when the loop induction is added.
-/

namespace CProverGOTO

open Imperative

public section

/-! ## Per-`Cmd` shape lemmas

Each lemma below characterises the result of one branch of
`Cmd.toGotoInstructions` when it succeeds. The conclusion pins down
exactly what `instructions` array is produced (a suffix appended to the
input `trans.instructions`) and how `nextLoc` advances.

### A note on the proof shape

The proofs use the pattern `match h_ty : G.toGotoType ty with | .ok gty
=> ...`. Inside the `.ok gty` arm, Lean's `match` substitutes the
discriminant `G.toGotoType ty` with `Except.ok gty` in the goal, so a
conclusion `G.toGotoType ty = Except.ok gty` reduces to `Except.ok gty
= Except.ok gty` (closed by `rfl`). After `simp only` reduces the
function body in `h`, an `injection`/`subst` extracts the concrete
output `GotoTransform`, after which the existential witnesses are the
literal record fields.
-/

/-- `.init v ty (.det e) md` succeeds iff `toGotoType ty` and
`toGotoExpr e` both succeed; the result has two new instructions
(DECL, ASSIGN) appended and `nextLoc` advanced by 2. -/
theorem Cmd_toGotoInstructions_init_det_ok
    (T : Core.Expression.TyEnv) (fname : String)
    (v : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h : Imperative.Cmd.toGotoInstructions T fname
          (.init v ty (.det e) md) trans = Except.ok ans) :
    ∃ gty e_goto i_decl i_assn,
      Imperative.ToGoto.toGotoType (P := Core.Expression) ty = Except.ok gty ∧
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e = Except.ok e_goto ∧
      i_decl.type = .DECL ∧
      i_decl.code = CProverGOTO.Code.decl
        (CProverGOTO.Expr.symbol
          (Imperative.ToGoto.identToString (P := Core.Expression) v) gty) ∧
      i_decl.locationNum = trans.nextLoc ∧
      i_assn.type = .ASSIGN ∧
      i_assn.code = CProverGOTO.Code.assign
        (CProverGOTO.Expr.symbol
          (Imperative.ToGoto.identToString (P := Core.Expression) v) gty) e_goto ∧
      i_assn.locationNum = trans.nextLoc + 1 ∧
      ans.instructions = trans.instructions.append #[i_decl, i_assn] ∧
      ans.nextLoc = trans.nextLoc + 2 ∧
      ans.T = Imperative.ToGoto.updateType (P := Core.Expression) T v ty := by
  unfold Imperative.Cmd.toGotoInstructions at h
  simp only at h
  match h_ty :
      Imperative.ToGoto.toGotoType (P := Core.Expression) ty with
  | .ok gty =>
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_ty, h_expr, Bind.bind, Except.bind, pure, Except.pure] at h
      injection h with h
      -- After simp, h_ty rewrote any `ToGoto.toGotoType ty` in the goal.
      -- Provide the explicit instructions matching the source code.
      refine ⟨gty, e_goto,
        { type := .DECL, locationNum := trans.nextLoc,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText,
          code := CProverGOTO.Code.decl
            (CProverGOTO.Expr.symbol
              (Imperative.ToGoto.identToString (P := Core.Expression) v) gty) },
        { type := .ASSIGN, locationNum := trans.nextLoc + 1,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText,
          code := CProverGOTO.Code.assign
            (CProverGOTO.Expr.symbol
              (Imperative.ToGoto.identToString (P := Core.Expression) v) gty) e_goto },
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      all_goals (subst h; rfl)
    | .error _ =>
      simp [h_ty, h_expr, Bind.bind, Except.bind] at h
  | .error _ =>
    simp [h_ty, Bind.bind, Except.bind] at h

/-- `.init v ty .nondet md` succeeds iff `toGotoType ty` succeeds;
the result has one new DECL appended and `nextLoc` advanced by 1. -/
theorem Cmd_toGotoInstructions_init_nondet_ok
    (T : Core.Expression.TyEnv) (fname : String)
    (v : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h : Imperative.Cmd.toGotoInstructions T fname
          (.init v ty .nondet md) trans = Except.ok ans) :
    ∃ gty i_decl,
      Imperative.ToGoto.toGotoType (P := Core.Expression) ty = Except.ok gty ∧
      i_decl.type = .DECL ∧
      i_decl.code = CProverGOTO.Code.decl
        (CProverGOTO.Expr.symbol
          (Imperative.ToGoto.identToString (P := Core.Expression) v) gty) ∧
      i_decl.locationNum = trans.nextLoc ∧
      ans.instructions = trans.instructions.push i_decl ∧
      ans.nextLoc = trans.nextLoc + 1 ∧
      ans.T = Imperative.ToGoto.updateType (P := Core.Expression) T v ty := by
  unfold Imperative.Cmd.toGotoInstructions at h
  simp only at h
  match h_ty :
      Imperative.ToGoto.toGotoType (P := Core.Expression) ty with
  | .ok gty =>
    simp only [h_ty, Bind.bind, Except.bind, pure, Except.pure] at h
    injection h with h
    refine ⟨gty,
      { type := .DECL, locationNum := trans.nextLoc,
        sourceLoc := metadataToSourceLoc md fname trans.sourceText,
        code := CProverGOTO.Code.decl
          (CProverGOTO.Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v) gty) },
      rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    all_goals (subst h; rfl)
  | .error _ =>
    simp [h_ty, Bind.bind, Except.bind] at h

/-- `.set v (.det e) md` succeeds iff `lookupType T v` and `toGotoExpr e`
both succeed; the result has one new ASSIGN appended and `nextLoc`
advanced by 1. -/
theorem Cmd_toGotoInstructions_set_det_ok
    (T : Core.Expression.TyEnv) (fname : String)
    (v : Core.Expression.Ident) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h : Imperative.Cmd.toGotoInstructions T fname
          (.set v (.det e) md) trans = Except.ok ans) :
    ∃ gty e_goto i_assn,
      Imperative.ToGoto.lookupType (P := Core.Expression) T v = Except.ok gty ∧
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e = Except.ok e_goto ∧
      i_assn.type = .ASSIGN ∧
      i_assn.code = CProverGOTO.Code.assign
        (CProverGOTO.Expr.symbol
          (Imperative.ToGoto.identToString (P := Core.Expression) v) gty) e_goto ∧
      i_assn.locationNum = trans.nextLoc ∧
      ans.instructions = trans.instructions.push i_assn ∧
      ans.nextLoc = trans.nextLoc + 1 := by
  unfold Imperative.Cmd.toGotoInstructions at h
  simp only at h
  match h_ty :
      Imperative.ToGoto.lookupType (P := Core.Expression) T v with
  | .ok gty =>
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_ty, h_expr, Bind.bind, Except.bind, pure, Except.pure] at h
      injection h with h
      refine ⟨gty, e_goto,
        { type := .ASSIGN, locationNum := trans.nextLoc,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText,
          code := CProverGOTO.Code.assign
            (CProverGOTO.Expr.symbol
              (Imperative.ToGoto.identToString (P := Core.Expression) v) gty) e_goto },
        rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      all_goals (subst h; rfl)
    | .error _ =>
      simp [h_ty, h_expr, Bind.bind, Except.bind] at h
  | .error _ =>
    simp [h_ty, Bind.bind, Except.bind] at h

/-- `.assert label e md` succeeds iff `toGotoExpr e` succeeds; the result
has one new ASSERT appended whose guard is the translated expression. -/
theorem Cmd_toGotoInstructions_assert_ok
    (T : Core.Expression.TyEnv) (fname : String)
    (label : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h : Imperative.Cmd.toGotoInstructions T fname
          (.assert label e md) trans = Except.ok ans) :
    ∃ e_goto i,
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e = Except.ok e_goto ∧
      i.type = .ASSERT ∧
      i.guard = e_goto ∧
      i.locationNum = trans.nextLoc ∧
      ans.instructions = trans.instructions.push i ∧
      ans.nextLoc = trans.nextLoc + 1 := by
  unfold Imperative.Cmd.toGotoInstructions at h
  simp only at h
  match h_expr :
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
  | .ok e_goto =>
    simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h
    injection h with h
    refine ⟨e_goto,
      { type := .ASSERT, locationNum := trans.nextLoc,
        sourceLoc := metadataToSourceLoc md fname trans.sourceText
          (comment := md.getPropertySummary.getD label),
        guard := e_goto },
      rfl, rfl, rfl, rfl, ?_, ?_⟩
    all_goals (subst h; rfl)
  | .error _ =>
    simp [h_expr, Bind.bind, Except.bind] at h

/-- `.assume label e md` succeeds iff `toGotoExpr e` succeeds; the result
has one new ASSUME appended whose guard is the translated expression. -/
theorem Cmd_toGotoInstructions_assume_ok
    (T : Core.Expression.TyEnv) (fname : String)
    (label : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h : Imperative.Cmd.toGotoInstructions T fname
          (.assume label e md) trans = Except.ok ans) :
    ∃ e_goto i,
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e = Except.ok e_goto ∧
      i.type = .ASSUME ∧
      i.guard = e_goto ∧
      i.locationNum = trans.nextLoc ∧
      ans.instructions = trans.instructions.push i ∧
      ans.nextLoc = trans.nextLoc + 1 := by
  unfold Imperative.Cmd.toGotoInstructions at h
  simp only at h
  match h_expr :
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
  | .ok e_goto =>
    simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h
    injection h with h
    refine ⟨e_goto,
      { type := .ASSUME, locationNum := trans.nextLoc,
        sourceLoc := metadataToSourceLoc md fname trans.sourceText
          (comment := label),
        guard := e_goto },
      rfl, rfl, rfl, rfl, ?_, ?_⟩
    all_goals (subst h; rfl)
  | .error _ =>
    simp [h_expr, Bind.bind, Except.bind] at h

/-! ## Emit-helper shape lemmas

These characterise the "small" emission helpers the translator uses
between command translations. They're definitionally true given the
helpers' definitions. -/

/-- `emitLabel` appends a single LOCATION instruction at the current
`nextLoc` and advances `nextLoc` by 1. -/
theorem emitLabel_shape
    {T : Type} (label : String) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform T) :
    let ans := Imperative.emitLabel label srcLoc trans
    ans.instructions = trans.instructions.push
      { type := .LOCATION, locationNum := trans.nextLoc,
        sourceLoc := srcLoc, labels := [label],
        code := CProverGOTO.Code.skip } ∧
    ans.nextLoc = trans.nextLoc + 1 := by
  exact ⟨rfl, rfl⟩

/-- `emitCondGoto` appends a single GOTO instruction with the given
guard and `target = none` at the current `nextLoc`. The returned index
is `trans.instructions.size`. -/
theorem emitCondGoto_shape
    {T : Type} (guard : CProverGOTO.Expr)
    (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform T) :
    let p := Imperative.emitCondGoto guard srcLoc trans
    p.snd = trans.instructions.size ∧
    p.fst.instructions = trans.instructions.push
      { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
        guard := guard, target := none } ∧
    p.fst.nextLoc = trans.nextLoc + 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- `emitUncondGoto` appends a single GOTO instruction with `guard =
Expr.true` and `target = none` at the current `nextLoc`. -/
theorem emitUncondGoto_shape
    {T : Type} (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform T) :
    let p := Imperative.emitUncondGoto srcLoc trans
    p.snd = trans.instructions.size ∧
    p.fst.instructions = trans.instructions.push
      { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
        guard := CProverGOTO.Expr.true, target := none } ∧
    p.fst.nextLoc = trans.nextLoc + 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## `patchGotoTargets` invariants

The second pass over `pendingPatches` mutates only the `target` field
of selected instructions. All other shape facts transfer unchanged
through patching. -/

/-- `Array.set!` preserves the array size on in-bounds indices and is a
no-op out of bounds — either way, size is preserved. -/
private theorem Array.size_set_eq {α} (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size := by
  by_cases h : i < a.size
  · simp [Array.set!, Array.setIfInBounds, h]
  · simp [Array.set!, Array.setIfInBounds, h]

/-- The instruction array length is preserved by `patchGotoTargets`. -/
theorem patchGotoTargets_preserves_size
    {T : Type} (trans : Imperative.GotoTransform T)
    (patches : List (Nat × Nat)) :
    (Imperative.patchGotoTargets trans patches).instructions.size =
      trans.instructions.size := by
  unfold Imperative.patchGotoTargets
  simp only
  -- Generalise over the array so the IH works on every fold-prefix.
  have hgen :
      ∀ (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat)),
        (List.foldl
          (fun acc (p : Nat × Nat) =>
            acc.set! p.fst { acc[p.fst]! with target := some p.snd })
          a ps).size = a.size := by
    intro a ps
    induction ps generalizing a with
    | nil => simp
    | cons p ps ih =>
      simp only [List.foldl]
      rw [ih]
      exact Array.size_set_eq _ _ _
  exact hgen _ _

/-- `patchGotoTargets` doesn't change the `nextLoc` field. -/
theorem patchGotoTargets_preserves_nextLoc
    {T : Type} (trans : Imperative.GotoTransform T)
    (patches : List (Nat × Nat)) :
    (Imperative.patchGotoTargets trans patches).nextLoc = trans.nextLoc := by
  unfold Imperative.patchGotoTargets
  rfl

/-- `patchGotoTargets` doesn't change the `T` field. -/
theorem patchGotoTargets_preserves_T
    {T : Type} (trans : Imperative.GotoTransform T)
    (patches : List (Nat × Nat)) :
    (Imperative.patchGotoTargets trans patches).T = trans.T := by
  unfold Imperative.patchGotoTargets
  rfl

/-! ## Instruction-array lookup helpers

The translator's loop produces instructions by repeatedly appending
suffixes; locating instruction `pc` in the final array reduces to
lookups in the pre-append prefix. The Lean core library provides
`Array.getElem?_push_lt`, `Array.getElem?_push_eq`,
`Array.getElem?_append_left`, `Array.getElem?_append_right` directly,
which we re-export here as a convenience for the loop-induction step. -/

/-- If `pgm.instructions = pre.push i` and `pre.size = pc`, then
`pgm.instrAt pc = some i`. -/
theorem instrAt_of_push
    (pgm : Program) (pre : Array Instruction) (i : Instruction) (pc : Nat)
    (h_eq : pgm.instructions = pre.push i)
    (h_size : pre.size = pc) :
    pgm.instrAt pc = some i := by
  unfold Program.instrAt
  rw [h_eq, ← h_size]
  exact Array.getElem?_push_size

/-- If `pgm.instructions = pre.push i` and `pc < pre.size`, then
the lookup at `pc` agrees with the lookup in `pre` (specifically,
returns `some (pre[pc])`). -/
theorem instrAt_of_push_lt
    (pgm : Program) (pre : Array Instruction) (i : Instruction) (pc : Nat)
    (h_pc : pc < pre.size)
    (h_eq : pgm.instructions = pre.push i) :
    pgm.instrAt pc = some pre[pc] := by
  unfold Program.instrAt
  rw [h_eq]
  exact Array.getElem?_push_lt h_pc

/-- If `pgm.instructions = pre.append #[i₀, i₁]` and `pre.size = pc`,
then `pgm.instrAt pc = some i₀` and `pgm.instrAt (pc + 1) = some i₁`.

Note this is the shape produced by the `init_det` case of
`Cmd.toGotoInstructions` (which appends a 2-element array of DECL +
ASSIGN). For the single-instruction emit cases we use `instrAt_of_push`. -/
theorem instrAt_of_append_two
    (pgm : Program) (pre : Array Instruction) (i₀ i₁ : Instruction) (pc : Nat)
    (h_eq : pgm.instructions = pre.append #[i₀, i₁])
    (h_size : pre.size = pc) :
    pgm.instrAt pc = some i₀ ∧ pgm.instrAt (pc + 1) = some i₁ := by
  unfold Program.instrAt
  -- Convert append to ++.
  have h_eq' : pgm.instructions = pre ++ #[i₀, i₁] := by
    rw [h_eq]
    rfl
  rw [h_eq', ← h_size]
  refine ⟨?_, ?_⟩
  · -- pc = pre.size; first slot of the suffix is i₀.
    have hge : pre.size ≤ pre.size := Nat.le_refl _
    rw [Array.getElem?_append_right hge]
    simp
  · -- pc + 1 = pre.size + 1; second slot of the suffix is i₁.
    have hge : pre.size ≤ pre.size + 1 := Nat.le_add_right _ _
    rw [Array.getElem?_append_right hge]
    simp

/-! ## Per-`Cmd` `CmdEmittedAt` builders

These are the bridges from the per-`Cmd` shape lemmas above to the
`CmdEmittedAt` predicate consumed by `WellFormedTranslation`. Each
takes:

* the result `ans` of `Cmd.toGotoInstructions` (matched via the
  corresponding shape lemma),
* an `ExprTranslated` witness for the relevant translated expression,
* a final program `pgm` whose `instructions` contains `ans.instructions`
  as a prefix (i.e., `pgm.instructions[k]? = ans.instructions[k]?` for
  every `k < ans.instructions.size`),

and produces `CmdEmittedAt pgm trans.nextLoc cmd`. The "prefix" form
abstracts away the patching pass and the trailing instructions emitted
by later blocks.

These builders are deliberately narrow — each handles exactly one of
the seven `Imperative.Cmd` constructors. The driver lemma that pieces
them together is part of the loop-induction work.
-/

/-- Bridge from `Cmd_toGotoInstructions_init_det_ok` to
`CmdEmittedAt.init_det`. -/
theorem cmdEmittedAt_init_det
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (pgm : Program) (pc : Nat)
    (v : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (e_core : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (i_decl i_assn : Instruction)
    (h_decl_at : pgm.instrAt pc = some i_decl)
    (h_decl_ty : i_decl.type = .DECL)
    (h_assn_at : pgm.instrAt (pc + 1) = some i_assn)
    (h_assn_ty : i_assn.type = .ASSIGN)
    (e_goto : Expr)
    (h_assn_code : ∃ lhs, i_assn.code = Code.assign lhs e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.init v ty (.det e_core) md) :=
  CmdEmittedAt.init_det pc v ty e_core md i_decl i_assn
    h_decl_at h_decl_ty h_assn_at h_assn_ty e_goto h_assn_code h_translated

/-- Bridge from `Cmd_toGotoInstructions_init_nondet_ok` to
`CmdEmittedAt.init_nondet`. -/
theorem cmdEmittedAt_init_nondet
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (pgm : Program) (pc : Nat)
    (v : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (md : Imperative.MetaData Core.Expression)
    (i_decl : Instruction)
    (h_decl_at : pgm.instrAt pc = some i_decl)
    (h_decl_ty : i_decl.type = .DECL) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.init v ty .nondet md) :=
  CmdEmittedAt.init_nondet pc v ty md i_decl h_decl_at h_decl_ty

/-- Bridge from `Cmd_toGotoInstructions_set_det_ok` to
`CmdEmittedAt.set_det`. -/
theorem cmdEmittedAt_set_det
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (pgm : Program) (pc : Nat)
    (v : Core.Expression.Ident) (e_core : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (i_assn : Instruction)
    (h_assn_at : pgm.instrAt pc = some i_assn)
    (h_assn_ty : i_assn.type = .ASSIGN)
    (e_goto : Expr)
    (h_assn_code : ∃ lhs, i_assn.code = Code.assign lhs e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v (.det e_core) md) :=
  CmdEmittedAt.set_det pc v e_core md i_assn
    h_assn_at h_assn_ty e_goto h_assn_code h_translated

/-- Bridge from `Cmd_toGotoInstructions_assert_ok` to
`CmdEmittedAt.assert_emit`. -/
theorem cmdEmittedAt_assert
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (pgm : Program) (pc : Nat)
    (label : String) (e_core : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (i : Instruction)
    (h_at : pgm.instrAt pc = some i)
    (h_ty : i.type = .ASSERT)
    (e_goto : Expr)
    (h_guard : i.guard = e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.assert label e_core md) :=
  CmdEmittedAt.assert_emit pc label e_core md i h_at h_ty
    e_goto h_guard h_translated

/-- Bridge from `Cmd_toGotoInstructions_assume_ok` to
`CmdEmittedAt.assume_emit`. -/
theorem cmdEmittedAt_assume
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (pgm : Program) (pc : Nat)
    (label : String) (e_core : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (i : Instruction)
    (h_at : pgm.instrAt pc = some i)
    (h_ty : i.type = .ASSUME)
    (e_goto : Expr)
    (h_guard : i.guard = e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.assume label e_core md) :=
  CmdEmittedAt.assume_emit pc label e_core md i h_at h_ty
    e_goto h_guard h_translated

/-! ## Per-`Cmd` lookup helper

`pgm_instrAt_of_push_invariant` is the building block used by the
per-`Cmd` driver below: it converts an `instructions = pre.push i`
shape into a `pgm.instrAt trans.nextLoc = some i` fact, given:
* the loop invariant `pre.size = trans.nextLoc`,
* the prefix property `pgm.instrAt k = some ans.instructions[k]` for
  the freshly-pushed slot `k = pre.size`. -/

theorem pgm_instrAt_of_push_invariant
    (pgm : Program) (pre : Array Instruction) (i : Instruction)
    (ans_instructions : Array Instruction) (nextLoc : Nat)
    (h_inv : pre.size = nextLoc)
    (h_inst : ans_instructions = pre.push i)
    (h_prefix :
      ∀ (k : Nat) (h : k < ans_instructions.size),
        pgm.instructions[k]? = some ans_instructions[k]) :
    pgm.instrAt nextLoc = some i := by
  have h_lt : nextLoc < ans_instructions.size := by
    rw [h_inst, Array.size_push, ← h_inv]; omega
  -- Look up at nextLoc in ans_instructions = pre.push i (where pre.size = nextLoc).
  have h_eq : ans_instructions[nextLoc]'h_lt = i := by
    subst h_inv h_inst
    exact Array.getElem_push_eq
  unfold Program.instrAt
  rw [h_prefix nextLoc h_lt, h_eq]

/-! ## Per-`Cmd` driver lemma

`cmdEmittedAt_of_toGotoInstructions_pushCases` packages the four
`Cmd.toGotoInstructions` cases that emit a *single* instruction
(set_det, assert, assume, init_nondet) into one drive-by lemma. The
two-instruction case (`init_det`) and the unsupported nondet-set case
need separate handling — a fuller driver expanding to all five cases
is the next step.

The lemma takes the loop invariant `trans.instructions.size =
trans.nextLoc` explicitly: this holds at the start (when
`trans.instructions = #[]` and `trans.nextLoc = 0`), and is preserved
by every emit-helper and `Cmd.toGotoInstructions` branch. -/

theorem cmdEmittedAt_assert_of_toGotoInstructions
    (T : Core.Expression.TyEnv) (fname : String)
    (label : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname
              (.assert label e md) trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq : Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
        = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc (.assert label e md) := by
  obtain ⟨e_goto, i, h_expr, h_ty, h_guard, _h_loc, h_inst, _h_next⟩ :=
    Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
  have h_at : pgm.instrAt trans.nextLoc = some i :=
    pgm_instrAt_of_push_invariant pgm trans.instructions i ans.instructions
      trans.nextLoc h_invariant h_inst h_prefix
  have h_tx_e : h_expr_corr.tx e = e_goto := by
    rw [h_tx_eq] at h_expr
    injection h_expr
  have h_translated : ExprTranslated δ δ_goto δ_goto_bool e e_goto := by
    rw [← h_tx_e]
    exact h_expr_corr.tx_correct e
  exact cmdEmittedAt_assert δ δ_goto δ_goto_bool pgm trans.nextLoc
    label e md i h_at h_ty e_goto h_guard h_translated

theorem cmdEmittedAt_assume_of_toGotoInstructions
    (T : Core.Expression.TyEnv) (fname : String)
    (label : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname
              (.assume label e md) trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq : Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
        = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc (.assume label e md) := by
  obtain ⟨e_goto, i, h_expr, h_ty, h_guard, _h_loc, h_inst, _h_next⟩ :=
    Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
  have h_at : pgm.instrAt trans.nextLoc = some i :=
    pgm_instrAt_of_push_invariant pgm trans.instructions i ans.instructions
      trans.nextLoc h_invariant h_inst h_prefix
  have h_tx_e : h_expr_corr.tx e = e_goto := by
    rw [h_tx_eq] at h_expr
    injection h_expr
  have h_translated : ExprTranslated δ δ_goto δ_goto_bool e e_goto := by
    rw [← h_tx_e]
    exact h_expr_corr.tx_correct e
  exact cmdEmittedAt_assume δ δ_goto δ_goto_bool pgm trans.nextLoc
    label e md i h_at h_ty e_goto h_guard h_translated

theorem cmdEmittedAt_set_det_of_toGotoInstructions
    (T : Core.Expression.TyEnv) (fname : String)
    (v : Core.Expression.Ident) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname
              (.set v (.det e) md) trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq : Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
        = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc (.set v (.det e) md) := by
  obtain ⟨gty, e_goto, i_assn, _h_ty, h_expr, h_assn_ty, h_assn_code,
    _h_assn_loc, h_inst, _h_next⟩ :=
    Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
  have h_at : pgm.instrAt trans.nextLoc = some i_assn :=
    pgm_instrAt_of_push_invariant pgm trans.instructions i_assn ans.instructions
      trans.nextLoc h_invariant h_inst h_prefix
  have h_tx_e : h_expr_corr.tx e = e_goto := by
    rw [h_tx_eq] at h_expr
    injection h_expr
  have h_translated : ExprTranslated δ δ_goto δ_goto_bool e e_goto := by
    rw [← h_tx_e]
    exact h_expr_corr.tx_correct e
  exact cmdEmittedAt_set_det δ δ_goto δ_goto_bool pgm trans.nextLoc
    v e md i_assn h_at h_assn_ty e_goto ⟨_, h_assn_code⟩ h_translated

theorem cmdEmittedAt_init_nondet_of_toGotoInstructions
    (T : Core.Expression.TyEnv) (fname : String)
    (v : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname
              (.init v ty .nondet md) trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc
      (.init v ty .nondet md) := by
  obtain ⟨gty, i_decl, _h_ty, h_decl_ty, _h_decl_code, _h_decl_loc,
    h_inst, _h_next, _h_T⟩ :=
    Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
  have h_at : pgm.instrAt trans.nextLoc = some i_decl :=
    pgm_instrAt_of_push_invariant pgm trans.instructions i_decl ans.instructions
      trans.nextLoc h_invariant h_inst h_prefix
  exact cmdEmittedAt_init_nondet δ δ_goto δ_goto_bool pgm trans.nextLoc
    v ty md i_decl h_at h_decl_ty

/-! ## Per-`Cmd` dispatcher

`cmdEmittedAt_of_toGotoInstructions` covers all five admitted single-step
shapes (init_nondet, set_det, assert, assume, cover) by case-splitting
on the inner `Cmd` and dispatching to the matching driver. The two
shapes outside the dispatcher are:

* `.init _ _ (.det _)`  — emits two instructions; covered by a separate
  driver below.
* `.set _ .nondet`      — admitted only when surfaced via the explicit
  builder `cmdEmittedAt_set_nondet`; the dispatcher below treats it as
  excluded so its caller doesn't have to thread an `isAdmittedCmd`
  predicate just for the `cover`/`set_nondet` cases.

The dispatcher's hypothesis `h_admitted` is `Core.CmdExt.isAdmittedCmd
(.cmd c) = true`, which excludes `cover` and `init _ _ .nondet` per
`isAdmittedCmd`'s definition. We *do* admit `.set _ .nondet`
syntactically here (the corresponding constructor of
`CmdEmittedAt.set_nondet` exists), even though the translator currently
does not produce that case in the call-free admitted fragment.
-/

/-- `cmdEmittedAt_of_toGotoInstructions` dispatches to the per-Cmd
driver matching the shape of `c`. The two-instruction case
(`.init _ _ (.det _)`) is *not* covered here — see
`cmdEmittedAt_init_det_of_toGotoInstructions` below. -/
theorem cmdEmittedAt_init_det_of_toGotoInstructions
    (T : Core.Expression.TyEnv) (fname : String)
    (v : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname
              (.init v ty (.det e) md) trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq : Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
        = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc
      (.init v ty (.det e) md) := by
  obtain ⟨gty, e_goto, i_decl, i_assn, _h_ty, h_expr,
          h_decl_ty, _h_decl_code, _h_decl_loc,
          h_assn_ty, h_assn_code, _h_assn_loc,
          h_inst, _h_next, _h_T⟩ :=
    Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
  -- Build a temporary program whose `instructions` field equals
  -- `ans.instructions = trans.instructions.append #[i_decl, i_assn]`,
  -- so that `instrAt_of_append_two` applies directly. The transfer
  -- to `pgm` then goes via `h_prefix`.
  let pgm_temp : Program := { pgm with instructions := ans.instructions }
  have h_pgm_temp : pgm_temp.instructions = ans.instructions := rfl
  have h_temp_eq : pgm_temp.instructions
      = trans.instructions.append #[i_decl, i_assn] := by
    rw [h_pgm_temp, h_inst]
  obtain ⟨h_at0_temp, h_at1_temp⟩ :=
    instrAt_of_append_two pgm_temp trans.instructions i_decl i_assn
      trans.nextLoc h_temp_eq h_invariant
  -- Convert pgm_temp.instrAt to ans.instructions[k]?, then to pgm.instrAt
  -- via h_prefix.
  have h_size_eq : ans.instructions.size = trans.instructions.size + 2 := by
    rw [h_inst]
    show (trans.instructions ++ #[i_decl, i_assn]).size = _
    rw [Array.size_append]
    simp
  have h_lt0 : trans.nextLoc < ans.instructions.size := by
    rw [h_size_eq, ← h_invariant]; omega
  have h_lt1 : trans.nextLoc + 1 < ans.instructions.size := by
    rw [h_size_eq, ← h_invariant]; omega
  -- pgm_temp.instrAt = ans.instructions[k]? for k < ans.instructions.size,
  -- by definition of instrAt and pgm_temp.
  have h_at0 : pgm.instrAt trans.nextLoc = some i_decl := by
    unfold Program.instrAt
    have h_eq : ans.instructions[trans.nextLoc]? = some i_decl := by
      have := h_at0_temp
      unfold Program.instrAt at this
      exact this
    rw [h_prefix trans.nextLoc h_lt0]
    rw [Array.getElem?_eq_getElem h_lt0] at h_eq
    exact h_eq
  have h_at1 : pgm.instrAt (trans.nextLoc + 1) = some i_assn := by
    unfold Program.instrAt
    have h_eq : ans.instructions[trans.nextLoc + 1]? = some i_assn := by
      have := h_at1_temp
      unfold Program.instrAt at this
      exact this
    rw [h_prefix (trans.nextLoc + 1) h_lt1]
    rw [Array.getElem?_eq_getElem h_lt1] at h_eq
    exact h_eq
  -- Translate the expression matching the translator's output.
  have h_tx_e : h_expr_corr.tx e = e_goto := by
    rw [h_tx_eq] at h_expr
    injection h_expr
  have h_translated : ExprTranslated δ δ_goto δ_goto_bool e e_goto := by
    rw [← h_tx_e]
    exact h_expr_corr.tx_correct e
  exact cmdEmittedAt_init_det δ δ_goto δ_goto_bool pgm trans.nextLoc
    v ty e md i_decl i_assn h_at0 h_decl_ty h_at1 h_assn_ty
    e_goto ⟨_, h_assn_code⟩ h_translated

/-! ## `set_nondet` shape and driver

Worker A's mechanical sub-lemmas covered the four single-instruction
emit cases that take an `ExprTranslated` witness. The `set _ .nondet`
case is structurally similar — single ASSIGN at `pc` — but with a
side-effect-Nondet RHS rather than a translated expression. Adding
the missing shape lemma + driver here unblocks the dispatcher. -/

/-- `.set v .nondet md` succeeds iff `lookupType T v` succeeds; the
result has one new ASSIGN appended whose RHS is a side-effect Nondet. -/
theorem Cmd_toGotoInstructions_set_nondet_ok
    (T : Core.Expression.TyEnv) (fname : String)
    (v : Core.Expression.Ident)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h : Imperative.Cmd.toGotoInstructions T fname
          (.set v .nondet md) trans = Except.ok ans) :
    ∃ gty i_assn,
      Imperative.ToGoto.lookupType (P := Core.Expression) T v = Except.ok gty ∧
      i_assn.type = .ASSIGN ∧
      (∃ lhs e_nondet, i_assn.code = Code.assign lhs e_nondet) ∧
      i_assn.locationNum = trans.nextLoc ∧
      ans.instructions = trans.instructions.push i_assn ∧
      ans.nextLoc = trans.nextLoc + 1 := by
  unfold Imperative.Cmd.toGotoInstructions at h
  simp only at h
  match h_ty :
      Imperative.ToGoto.lookupType (P := Core.Expression) T v with
  | .ok gty =>
    simp only [h_ty, Bind.bind, Except.bind, pure, Except.pure] at h
    injection h with h
    let srcLoc := metadataToSourceLoc md fname trans.sourceText
    refine ⟨gty,
      { type := .ASSIGN, locationNum := trans.nextLoc,
        sourceLoc := srcLoc,
        code := CProverGOTO.Code.assign
          (CProverGOTO.Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v) gty)
          { id := .side_effect .Nondet, sourceLoc := srcLoc, type := gty } },
      rfl, rfl, ⟨_, _, rfl⟩, rfl, ?_, ?_⟩
    all_goals (subst h; rfl)
  | .error _ =>
    simp [h_ty, Bind.bind, Except.bind] at h

/-- Bridge from `Cmd_toGotoInstructions_set_nondet_ok` to
`CmdEmittedAt.set_nondet`. -/
theorem cmdEmittedAt_set_nondet
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (pgm : Program) (pc : Nat)
    (v : Core.Expression.Ident)
    (md : Imperative.MetaData Core.Expression)
    (i_assn : Instruction)
    (h_assn_at : pgm.instrAt pc = some i_assn)
    (h_assn_ty : i_assn.type = .ASSIGN)
    (h_assn_code : ∃ lhs e_nondet, i_assn.code = Code.assign lhs e_nondet) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v .nondet md) :=
  CmdEmittedAt.set_nondet pc v md i_assn h_assn_at h_assn_ty h_assn_code

theorem cmdEmittedAt_set_nondet_of_toGotoInstructions
    (T : Core.Expression.TyEnv) (fname : String)
    (v : Core.Expression.Ident)
    (md : Imperative.MetaData Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname
              (.set v .nondet md) trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc (.set v .nondet md) := by
  obtain ⟨_gty, i_assn, _h_ty, h_assn_ty, h_assn_code, _h_loc, h_inst, _h_next⟩ :=
    Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
  have h_at : pgm.instrAt trans.nextLoc = some i_assn :=
    pgm_instrAt_of_push_invariant pgm trans.instructions i_assn ans.instructions
      trans.nextLoc h_invariant h_inst h_prefix
  exact cmdEmittedAt_set_nondet δ δ_goto δ_goto_bool pgm trans.nextLoc
    v md i_assn h_at h_assn_ty h_assn_code

/-! ## Per-Cmd dispatcher

The dispatcher case-splits on an `Imperative.Cmd Core.Expression`
admitted by `isAdmittedCmd` and produces a `CmdEmittedAt` witness from
a successful `Cmd.toGotoInstructions` call. It uses the per-shape
drivers above (`cmdEmittedAt_init_det_of_toGotoInstructions`,
`cmdEmittedAt_init_nondet_of_toGotoInstructions`,
`cmdEmittedAt_set_det_of_toGotoInstructions`,
`cmdEmittedAt_assert_of_toGotoInstructions`,
`cmdEmittedAt_assume_of_toGotoInstructions`).

The translator never emits `.cover` (excluded by `isAdmittedCmd`) nor
`.set _ .nondet` (excluded under the same flag); both cases are
discharged contradictorily from `h_admitted`.
-/

theorem cmdEmittedAt_of_toGotoInstructions
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (h_admitted : Core.CmdExt.isAdmittedCmd (.cmd c) = true)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc c := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      exact cmdEmittedAt_init_det_of_toGotoInstructions
        T fname v ty e md trans ans h_run h_invariant
        pgm δ δ_goto δ_goto_bool h_expr_corr (h_tx_eq e) h_prefix
    | nondet =>
      -- `init _ _ .nondet` is excluded by `isAdmittedCmd`.
      simp [Core.CmdExt.isAdmittedCmd] at h_admitted
  | set v src md =>
    cases src with
    | det e =>
      exact cmdEmittedAt_set_det_of_toGotoInstructions
        T fname v e md trans ans h_run h_invariant
        pgm δ δ_goto δ_goto_bool h_expr_corr (h_tx_eq e) h_prefix
    | nondet =>
      -- `set _ .nondet` is admitted under `isAdmittedCmd` but the
      -- caller (loop-induction) treats it specially because it has a
      -- different RHS shape. We could discharge it via a
      -- `cmdEmittedAt_set_nondet_of_toGotoInstructions` driver — for
      -- now we leave this as a documented gap because the parallel-A
      -- run did not land that driver. The pattern is identical to
      -- the `set_det` driver minus the `ExprTranslated` witness.
      exact cmdEmittedAt_set_nondet_of_toGotoInstructions
        T fname v md trans ans h_run h_invariant pgm
        δ δ_goto δ_goto_bool h_prefix
  | assert label e md =>
    exact cmdEmittedAt_assert_of_toGotoInstructions
      T fname label e md trans ans h_run h_invariant
      pgm δ δ_goto δ_goto_bool h_expr_corr (h_tx_eq e) h_prefix
  | assume label e md =>
    exact cmdEmittedAt_assume_of_toGotoInstructions
      T fname label e md trans ans h_run h_invariant
      pgm δ δ_goto δ_goto_bool h_expr_corr (h_tx_eq e) h_prefix
  | cover label e md =>
    -- `cover` is excluded by `isAdmittedCmd`.
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-! ## Loop invariant for `coreCFGToGotoTransform`'s outer for-loop

`PartialWellFormedTranslation` is a "prefix" version of
`WellFormedTranslation` indexed by the number of CFG blocks already
processed. It's the natural induction hypothesis for the outer loop.

Differences from `WellFormedTranslation`:

* `cfg.blocks` is replaced by `cfg.blocks.take n` (the prefix processed
  so far) wherever the predicate quantifies "for each block".
* `labelMap_total` is restricted to the prefix.
* The `entry_in_map` field is dropped (the entry block may not yet have
  been processed when `n = 0`); we recover it after the full iteration
  by noting `n = cfg.blocks.length` and that the entry block is in
  `cfg.blocks` (an external well-formedness assumption on `cfg`).
* `pendingPatches` is carried explicitly: each pending patch records
  a forward GOTO target that hasn't yet been resolved.

The translator's iteration produces a `PartialWellFormedTranslation`
after `n` iterations; the patch pass at the end converts this (with
`n = cfg.blocks.length`) into a full `WellFormedTranslation`. -/

/-- The invariant carried by `coreCFGToGotoTransform`'s outer for-loop
through `n` iterations. Quantifies layout fields over
`cfg.blocks.take n` instead of all of `cfg.blocks`. -/
structure PartialWellFormedTranslation
    (cfg : Core.DetCFG)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : LabelMap)
    (n : Nat)
    (_δ : Imperative.SemanticEval Core.Expression)
    (_δ_goto : SemanticEvalGoto Core.Expression)
    (_δ_goto_bool : SemanticEvalGotoBool Core.Expression) : Prop where
  /-- The transform's `instructions.size = nextLoc` invariant: every
  emit-helper advances both by the same amount. -/
  size_eq : trans.instructions.size = trans.nextLoc
  /-- Every instruction emitted so far has `locationNum = index`. -/
  locationNum_eq_index :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      trans.instructions[i]? = some instr → instr.locationNum = i
  /-- Every block label in the processed prefix has a `pc` in `labelMap`. -/
  labelMap_total :
    ∀ l, l ∈ (cfg.blocks.take n).map Prod.fst → (labelMap l).isSome
  /-- Distinct labels map to distinct `pc`s. -/
  labelMap_inj :
    ∀ l₁ l₂ pc, labelMap l₁ = some pc → labelMap l₂ = some pc → l₁ = l₂
  /-- The labelMap's image is contained in the current range
  `[0, trans.nextLoc)`. -/
  labelMap_lt :
    ∀ l pc, labelMap l = some pc → pc < trans.nextLoc

/-! ## Initial-state `PartialWellFormedTranslation`

At the start of the outer loop (before any iteration), `n = 0`,
`labelMap = (fun _ => none)` (empty), and `trans` is the entry-state
transform produced by the wrapper. The partial WF holds vacuously for
all the prefix-quantified fields. -/

/-- An empty `LabelMap`: returns `none` for every label. -/
@[expose] def emptyLabelMap : LabelMap := fun _ => none

/-- The initial state (before any block has been processed) satisfies
`PartialWellFormedTranslation` with `n = 0` whenever the entry-state
`trans` already has its instruction array's `locationNum`s aligned with
their indices. The wrapper `procedureToGotoCtxViaCFG` ensures this by
constructing the axiom-emit prologue with `locationNum = axiomLoc` and
`axiomLoc = i` for each emitted axiom. -/
theorem partialWellFormedTranslation_initial
    (cfg : Core.DetCFG)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression) :
    PartialWellFormedTranslation cfg trans emptyLabelMap 0
      δ δ_goto δ_goto_bool where
  size_eq := h_size
  locationNum_eq_index := h_loc
  labelMap_total := by
    intro l h_in
    simp at h_in
  labelMap_inj := by
    intro l₁ l₂ pc h₁ _h₂
    simp [emptyLabelMap] at h₁
  labelMap_lt := by
    intro l pc h
    simp [emptyLabelMap] at h

/-! ## Preservation under `emitLabel`

The outer loop body starts each iteration by emitting a LOCATION
instruction via `emitLabel`. We need to know that this preserves the
`size_eq` and `locationNum_eq_index` invariants, and that the new
`labelMap` (extended with `label ↦ trans.nextLoc`) keeps the partial
WF working. -/

/-- After `emitLabel`, the new transform's `instructions.size` still
equals its `nextLoc` (each goes up by 1). -/
theorem emitLabel_preserves_size_eq
    (label : String) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc) :
    (Imperative.emitLabel label srcLoc trans).instructions.size =
      (Imperative.emitLabel label srcLoc trans).nextLoc := by
  simp [Imperative.emitLabel, Array.size_push, h_size]

/-- After `emitLabel`, the new transform's `locationNum`s still match
their array indices: the existing prefix is preserved, and the
freshly-pushed LOCATION has `locationNum = trans.nextLoc =
trans.instructions.size`. -/
theorem emitLabel_preserves_locationNum_eq_index
    (label : String) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (Imperative.emitLabel label srcLoc trans).instructions[i]? = some instr →
      instr.locationNum = i := by
  intro i instr h
  -- Compute `(emitLabel ..).instructions` as a `push` so the rewrite
  -- patterns apply.
  let new_instr : CProverGOTO.Instruction :=
    { type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      labels := [label], code := CProverGOTO.Code.skip }
  have h_unfold : (Imperative.emitLabel label srcLoc trans).instructions
      = trans.instructions.push new_instr := by rfl
  rw [h_unfold] at h
  by_cases h_lt : i < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h
    -- h : some trans.instructions[i] = some instr
    have h' : trans.instructions[i]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h
    exact h_loc i instr h'
  · have h_ge : trans.instructions.size ≤ i := Nat.le_of_not_lt h_lt
    by_cases h_eq : i = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h
      injection h with h
      subst h
      show new_instr.locationNum = trans.instructions.size
      simp [new_instr, h_size]
    · have h_lt' : trans.instructions.size < i := by omega
      have h_push_size :
          (trans.instructions.push new_instr).size = trans.instructions.size + 1 := by
        simp [Array.size_push]
      have h_oor : (trans.instructions.push new_instr).size ≤ i := by
        rw [h_push_size]; omega
      rw [Array.getElem?_eq_none h_oor] at h
      exact absurd h (by simp)

/-! ## Preservation under `Cmd.toGotoInstructions`

After processing one Core command via the imperative
`Cmd.toGotoInstructions`, the resulting `trans'` still satisfies the
`size_eq` and `locationNum_eq_index` invariants. Because each branch of
`Cmd.toGotoInstructions` either pushes one or two instructions and
advances `nextLoc` by the same number (provided by the per-shape
sub-lemmas above), the calculation is direct. -/

/-- `Cmd.toGotoInstructions` preserves `instructions.size = nextLoc`. -/
theorem toGotoInstructions_preserves_size_eq
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_gty, _e_goto, _i_decl, _i_assn, _, _, _, _, _, _, _, _,
              h_inst, h_next, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst, h_next]
      show (trans.instructions ++ #[_, _]).size = _
      simp [Array.size_append, h_size]
    | nondet =>
      obtain ⟨_gty, _i_decl, _, _, _, _, h_inst, h_next, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst, h_next, Array.size_push, h_size]
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_gty, _e_goto, _i_assn, _, _, _, _, _, h_inst, h_next⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst, h_next, Array.size_push, h_size]
    | nondet =>
      obtain ⟨_gty, _i_assn, _, _, _, _, h_inst, h_next⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst, h_next, Array.size_push, h_size]
  | assert label e md =>
    obtain ⟨_e_goto, _i, _, _, _, _, h_inst, h_next⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst, h_next, Array.size_push, h_size]
  | assume label e md =>
    obtain ⟨_e_goto, _i, _, _, _, _, h_inst, h_next⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst, h_next, Array.size_push, h_size]
  | cover label e md =>
    -- `cover` is structurally similar to `assert` but emits an ASSERT
    -- with a different comment. The shape lemma was not landed by
    -- Worker A; for the size-preservation argument we directly unfold.
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      subst h_run
      simp [Array.size_push, h_size]
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- Generic helper: pushing one fresh instruction whose `locationNum =
trans.nextLoc` preserves `locationNum_eq_index`, given the loop
invariant. -/
private theorem push_preserves_locationNum_eq_index
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (new_instr : CProverGOTO.Instruction)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i)
    (h_new : new_instr.locationNum = trans.nextLoc) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (trans.instructions.push new_instr)[i]? = some instr →
      instr.locationNum = i := by
  intro i instr h
  by_cases h_lt : i < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h
    have h' : trans.instructions[i]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h
    exact h_loc i instr h'
  · have h_ge : trans.instructions.size ≤ i := Nat.le_of_not_lt h_lt
    by_cases h_eq : i = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h
      injection h with h
      subst h
      rw [h_new, h_size]
    · have h_lt' : trans.instructions.size < i := by omega
      have h_oor : (trans.instructions.push new_instr).size ≤ i := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h
      exact absurd h (by simp)

/-- Generic helper: appending two fresh instructions whose `locationNum`
fields are `trans.nextLoc` and `trans.nextLoc + 1` preserves
`locationNum_eq_index`. Used for the `init_det` case. -/
private theorem append_two_preserves_locationNum_eq_index
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (i₀ i₁ : CProverGOTO.Instruction)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i)
    (h_new0 : i₀.locationNum = trans.nextLoc)
    (h_new1 : i₁.locationNum = trans.nextLoc + 1) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (trans.instructions.append #[i₀, i₁])[i]? = some instr →
      instr.locationNum = i := by
  intro i instr h
  -- Replace .append with `++ #[i₀, i₁]`.
  have h_eq : trans.instructions.append #[i₀, i₁]
      = trans.instructions ++ #[i₀, i₁] := rfl
  rw [h_eq] at h
  by_cases h_lt : i < trans.instructions.size
  · rw [Array.getElem?_append_left h_lt] at h
    exact h_loc i instr h
  · have h_ge : trans.instructions.size ≤ i := Nat.le_of_not_lt h_lt
    by_cases h_eq0 : i = trans.instructions.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h
      simp at h
      subst h
      rw [h_new0, h_size]
    · by_cases h_eq1 : i = trans.instructions.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h
        simp at h
        subst h
        rw [h_new1, h_size]
      · -- i > size + 1: out of bounds.
        have h_oor : (trans.instructions ++ #[i₀, i₁]).size ≤ i := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h
        exact absurd h (by simp)

/-- `Cmd.toGotoInstructions` preserves `locationNum_eq_index` on the
emitted prefix. -/
theorem toGotoInstructions_preserves_locationNum_eq_index
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_gty, _e_goto, i_decl, i_assn, _, _, _, _, h_decl_loc,
              _, _, h_assn_loc, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst]
      exact append_two_preserves_locationNum_eq_index
        trans i_decl i_assn h_size h_loc h_decl_loc h_assn_loc
    | nondet =>
      obtain ⟨_gty, i_decl, _, _, _, h_loc_new, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst]
      exact push_preserves_locationNum_eq_index
        trans i_decl h_size h_loc h_loc_new
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_gty, _e_goto, i_assn, _, _, _, _, h_loc_new, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst]
      exact push_preserves_locationNum_eq_index
        trans i_assn h_size h_loc h_loc_new
    | nondet =>
      obtain ⟨_gty, i_assn, _, _, _, h_loc_new, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst]
      exact push_preserves_locationNum_eq_index
        trans i_assn h_size h_loc h_loc_new
  | assert label e md =>
    obtain ⟨_e_goto, i, _, _, _, h_loc_new, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst]
    exact push_preserves_locationNum_eq_index
      trans i h_size h_loc h_loc_new
  | assume label e md =>
    obtain ⟨_e_goto, i, _, _, _, h_loc_new, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst]
    exact push_preserves_locationNum_eq_index
      trans i h_size h_loc h_loc_new
  | cover label e md =>
    -- Direct unfold + push.
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      subst h_run
      -- ans.instructions = trans.instructions.push assert_inst
      -- where assert_inst.locationNum = trans.nextLoc.
      apply push_preserves_locationNum_eq_index trans _ h_size h_loc
      rfl
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-! ## Preservation under transfer-emit helpers -/

/-- `emitCondGoto` preserves `instructions.size = nextLoc`. -/
theorem emitCondGoto_preserves_size_eq
    (guard : CProverGOTO.Expr) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc) :
    let p := Imperative.emitCondGoto guard srcLoc trans
    p.fst.instructions.size = p.fst.nextLoc := by
  simp [Imperative.emitCondGoto, Imperative.emitGoto, Array.size_push, h_size]

/-- `emitCondGoto` preserves `locationNum_eq_index`. -/
theorem emitCondGoto_preserves_locationNum_eq_index
    (guard : CProverGOTO.Expr) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (Imperative.emitCondGoto guard srcLoc trans).fst.instructions[i]? =
        some instr →
      instr.locationNum = i := by
  intro i instr h
  let new_instr : CProverGOTO.Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := guard, target := none }
  have h_unfold : (Imperative.emitCondGoto guard srcLoc trans).fst.instructions
      = trans.instructions.push new_instr := by rfl
  rw [h_unfold] at h
  exact push_preserves_locationNum_eq_index trans new_instr
    h_size h_loc rfl i instr h

/-- `emitUncondGoto` preserves `instructions.size = nextLoc`. -/
theorem emitUncondGoto_preserves_size_eq
    (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc) :
    let p := Imperative.emitUncondGoto srcLoc trans
    p.fst.instructions.size = p.fst.nextLoc := by
  simp [Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push, h_size]

/-- `emitUncondGoto` preserves `locationNum_eq_index`. -/
theorem emitUncondGoto_preserves_locationNum_eq_index
    (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (Imperative.emitUncondGoto srcLoc trans).fst.instructions[i]? =
        some instr →
      instr.locationNum = i := by
  intro i instr h
  let new_instr : CProverGOTO.Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := CProverGOTO.Expr.true, target := none }
  have h_unfold : (Imperative.emitUncondGoto srcLoc trans).fst.instructions
      = trans.instructions.push new_instr := by rfl
  rw [h_unfold] at h
  exact push_preserves_locationNum_eq_index trans new_instr
    h_size h_loc rfl i instr h

/-! ## Preservation under `END_FUNCTION` emission

The `.finish` branch of `coreCFGToGotoTransform`'s outer-loop body
inlines an END_FUNCTION emit (no helper exists), so we model it
directly as a push of an instruction with the right shape. -/

/-- The shape of the `.finish md` branch's emitted END_FUNCTION
instruction. The translator hardcodes:
* `type = .END_FUNCTION`,
* `locationNum = trans.nextLoc`,
* `sourceLoc = metadataToSourceLoc md fname trans.sourceText`. -/
@[expose] def endFunctionInstr
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    CProverGOTO.Instruction :=
  { type := .END_FUNCTION,
    locationNum := trans.nextLoc,
    sourceLoc := Imperative.metadataToSourceLoc md fname trans.sourceText }

/-- After the `.finish` branch's END_FUNCTION emit, the new transform
satisfies `instructions.size = nextLoc`. -/
theorem endFunction_emit_preserves_size_eq
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc) :
    let trans' : Imperative.GotoTransform Core.Expression.TyEnv :=
      { trans with
        instructions := trans.instructions.push (endFunctionInstr md fname trans),
        nextLoc := trans.nextLoc + 1 }
    trans'.instructions.size = trans'.nextLoc := by
  simp [Array.size_push, h_size]

/-- `END_FUNCTION` emit preserves `locationNum_eq_index`. -/
theorem endFunction_emit_preserves_locationNum_eq_index
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (trans.instructions.push (endFunctionInstr md fname trans))[i]? =
        some instr →
      instr.locationNum = i :=
  push_preserves_locationNum_eq_index trans (endFunctionInstr md fname trans)
    h_size h_loc rfl

/-! ## Preservation under `patchGotoTargets`

The patcher only edits `target` fields, never `locationNum`s. So the
`locationNum_eq_index` invariant transfers unchanged. -/

/-- `Array.set!` with a record update on `target` doesn't change
`locationNum`. -/
private theorem patch_one_preserves_locationNum
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        a[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr →
      instr.locationNum = i := by
  intro i instr h
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases h_idx : idx < a.size
  · -- Set at in-bounds idx via setIfInBounds.
    by_cases h_eq : i = idx
    · subst h_eq
      have h_lt_set :
          i < (a.setIfInBounds i { a[i]! with target := some tgt }).size := by
        simp [h_idx]
      rw [Array.getElem?_eq_getElem h_lt_set] at h
      rw [Array.getElem_setIfInBounds_self] at h
      injection h with h
      subst h
      -- The patched record's locationNum = a[i]!.locationNum.
      -- And a[i]!.locationNum = a[i].locationNum (in-bounds) = i by h_loc.
      have h_at : a[i]? = some a[i] := Array.getElem?_eq_getElem h_idx
      have h_loc_eq : a[i].locationNum = i := h_loc i a[i] h_at
      have h_getD : a[i]! = a[i] := getElem!_pos a i h_idx
      simp [h_getD, h_loc_eq]
    · -- i ≠ idx: setIfInBounds preserves a[i]?.
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)] at h
      exact h_loc i instr h
  · -- idx out of range: setIfInBounds is a no-op.
    rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)] at h
    exact h_loc i instr h

/-- `Array.set!` with a record update on `target` preserves the
type field. -/
private theorem patch_one_preserves_type
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr) :
    ∃ instr_pre,
      a[i]? = some instr_pre ∧
      instr.type = instr_pre.type := by
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases h_idx : idx < a.size
  · by_cases h_eq : i = idx
    · subst h_eq
      have h_lt_set : i < (a.setIfInBounds i { a[i]! with target := some tgt }).size := by
        simp [h_idx]
      rw [Array.getElem?_eq_getElem h_lt_set] at h
      rw [Array.getElem_setIfInBounds_self] at h
      injection h with h
      have h_at : a[i]? = some a[i] := Array.getElem?_eq_getElem h_idx
      refine ⟨a[i], h_at, ?_⟩
      have h_getD : a[i]! = a[i] := getElem!_pos a i h_idx
      rw [← h]
      simp [h_getD]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)] at h
      exact ⟨instr, h, rfl⟩
  · rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)] at h
    exact ⟨instr, h, rfl⟩

/-- `patchGotoTargets` preserves the type field at any in-bounds
index — the patcher only writes the `target` field. -/
theorem patchGotoTargets_preserves_type
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr) :
    ∃ instr_pre,
      trans.instructions[i]? = some instr_pre ∧
      instr.type = instr_pre.type := by
  unfold Imperative.patchGotoTargets at h
  simp only at h
  -- Generalize over the array.
  have hgen :
      ∀ (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
        (i : Nat) (instr : CProverGOTO.Instruction),
        (List.foldl
          (fun acc (p : Nat × Nat) =>
            acc.set! p.fst { acc[p.fst]! with target := some p.snd })
          a ps)[i]? = some instr →
        ∃ instr_pre, a[i]? = some instr_pre ∧ instr.type = instr_pre.type := by
    intro a ps i instr h
    induction ps generalizing a with
    | nil =>
      simp at h
      exact ⟨instr, h, rfl⟩
    | cons p ps ih =>
      simp only [List.foldl] at h
      obtain ⟨instr_after_first, h_after_first, h_ty_after_first⟩ := ih _ h
      obtain ⟨instr_pre, h_pre, h_ty_pre⟩ :=
        patch_one_preserves_type a p.1 p.2 i instr_after_first h_after_first
      exact ⟨instr_pre, h_pre, h_ty_after_first.trans h_ty_pre⟩
  exact hgen _ _ _ _ h

/-- `patchGotoTargets` preserves `locationNum_eq_index` on the underlying
array — the patcher only writes the `target` field. -/
theorem patchGotoTargets_preserves_locationNum_eq_index
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr →
      instr.locationNum = i := by
  -- Generalise so the IH works at every prefix.
  unfold Imperative.patchGotoTargets
  simp only
  -- We're in the foldl shape now; induct on patches.
  intro i instr
  -- A more general statement: for any `a` satisfying `h_loc`, the
  -- foldl over `patches` preserves `h_loc`.
  have hgen :
      ∀ (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
        (h : ∀ (i : Nat) (instr : CProverGOTO.Instruction),
          a[i]? = some instr → instr.locationNum = i),
        ∀ (i : Nat) (instr : CProverGOTO.Instruction),
          (List.foldl
            (fun acc (p : Nat × Nat) =>
              acc.set! p.fst { acc[p.fst]! with target := some p.snd })
            a ps)[i]? = some instr → instr.locationNum = i := by
    intro a ps h
    induction ps generalizing a with
    | nil =>
      intro i instr h2
      simp only [List.foldl] at h2
      exact h i instr h2
    | cons p ps ih =>
      intro i instr h2
      simp only [List.foldl] at h2
      apply ih (a.set! p.fst { a[p.fst]! with target := some p.snd })
        (patch_one_preserves_locationNum a p.fst p.snd h)
      exact h2
  exact hgen _ _ h_loc i instr

/-! ## Inner-loop shadow: a foldlM over the admitted `.cmd c` cases

The `coreCFGToGotoTransform`'s inner `for cmd in block.cmds do` loop is
imperative and dispatches on `cmd.cmd / cmd.call`. Under the
admitted-commands fragment (`isAdmittedCmd`), only the `.cmd c` branch
is taken, so the inner loop is morally a `foldlM` of
`Cmd.toGotoInstructions` over the `c`-extractions of `block.cmds`.

We give this a clean recursive name here, and prove that the empty
list and inductive step both preserve the loop invariants we care
about. -/

/-- Run `Cmd.toGotoInstructions` on each admitted `.cmd c` of a block's
command list, threading the transform state. Errors out on any
non-admitted command. -/
@[expose] def innerCmdLoop
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    Except Std.Format (Imperative.GotoTransform Core.Expression.TyEnv) :=
  match cmds with
  | [] => Except.ok trans
  | .cmd c :: rest => do
    let trans' ← (Imperative.Cmd.toGotoInstructions T fname c trans).mapError
      (fun e => f!"{e}")
    innerCmdLoop trans'.T fname rest trans'
  | .call _ _ _ :: _ =>
    Except.error f!"[innerCmdLoop] .call is not in the admitted fragment"

/-- Empty body: the inner loop is a no-op. -/
theorem innerCmdLoop_nil
    (T : Core.Expression.TyEnv) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    innerCmdLoop T fname [] trans = Except.ok trans := rfl

/-- The inner loop preserves the size invariant. -/
theorem innerCmdLoop_preserves_size_eq
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  induction cmds generalizing T trans with
  | nil =>
    rw [innerCmdLoop_nil] at h_run
    injection h_run with h_run
    rw [← h_run]; exact h_size
  | cons cmd rest ih =>
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        have h_size' : trans'.instructions.size = trans'.nextLoc :=
          toGotoInstructions_preserves_size_eq T fname c trans trans' h_step h_size
        exact ih trans'.T trans' h_run h_size'
      | .error e =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      unfold innerCmdLoop at h_run
      simp at h_run

/-- The inner loop preserves the locationNum_eq_index invariant. -/
theorem innerCmdLoop_preserves_locationNum_eq_index
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  induction cmds generalizing T trans with
  | nil =>
    rw [innerCmdLoop_nil] at h_run
    injection h_run with h_run
    rw [← h_run]; exact h_loc
  | cons cmd rest ih =>
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        have h_size' : trans'.instructions.size = trans'.nextLoc :=
          toGotoInstructions_preserves_size_eq T fname c trans trans' h_step h_size
        have h_loc' :
            ∀ (i : Nat) (instr : CProverGOTO.Instruction),
              trans'.instructions[i]? = some instr → instr.locationNum = i :=
          toGotoInstructions_preserves_locationNum_eq_index
            T fname c trans trans' h_step h_size h_loc
        exact ih trans'.T trans' h_run h_size' h_loc'
      | .error e =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      unfold innerCmdLoop at h_run
      simp at h_run

/-- The inner loop's `nextLoc` advance equals the per-cmd instruction
counts summed. Specifically, `ans.nextLoc = trans.nextLoc + Σ
gotoInstrCount`, where the sum is over each admitted command. This is
the analogue of `cmdsPrefixInstrCount` and is what `layout_block_body`
needs to address each command's emitted slot. -/
theorem innerCmdLoop_nextLoc_advance
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans) :
    ans.nextLoc = trans.nextLoc +
      cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 := by
  induction cmds generalizing T trans with
  | nil =>
    rw [innerCmdLoop_nil] at h_run
    injection h_run with h_run
    simp [← h_run]
  | cons cmd rest ih =>
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        -- Per-cmd nextLoc advance from each shape lemma, dispatched by `c`.
        have h_step_advance :
            trans'.nextLoc = trans.nextLoc + Imperative.Cmd.gotoInstrCount c := by
          cases c with
          | init v ty init md =>
            cases init with
            | det e =>
              obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h_next, _⟩ :=
                Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans trans' h_step
              rw [h_next]; rfl
            | nondet =>
              obtain ⟨_, _, _, _, _, _, _, h_next, _⟩ :=
                Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans trans' h_step
              rw [h_next]; rfl
          | set v src md =>
            cases src with
            | det e =>
              obtain ⟨_, _, _, _, _, _, _, _, _, h_next⟩ :=
                Cmd_toGotoInstructions_set_det_ok T fname v e md trans trans' h_step
              rw [h_next]; rfl
            | nondet =>
              obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
                Cmd_toGotoInstructions_set_nondet_ok T fname v md trans trans' h_step
              rw [h_next]; rfl
          | assert label e md =>
            obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
              Cmd_toGotoInstructions_assert_ok T fname label e md trans trans' h_step
            rw [h_next]; rfl
          | assume label e md =>
            obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
              Cmd_toGotoInstructions_assume_ok T fname label e md trans trans' h_step
            rw [h_next]; rfl
          | cover label e md =>
            unfold Imperative.Cmd.toGotoInstructions at h_step
            simp only at h_step
            match h_expr :
                Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
            | .ok e_goto =>
              simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_step
              injection h_step with h_step
              rw [← h_step]
              rfl
            | .error _ =>
              simp [h_expr, Bind.bind, Except.bind] at h_step
        have hih := ih trans'.T trans' h_run
        rw [hih, h_step_advance]
        -- Goal: trans.nextLoc + count(c) + foldl 0 rest =
        --       trans.nextLoc + foldl 0 ((Core.CmdExt.cmd c) :: rest).
        -- The cons case of foldl: foldl init ((Core.CmdExt.cmd c) :: rest) =
        -- foldl (init + Core.CmdExt.gotoInstrCount (Core.CmdExt.cmd c)) rest =
        -- foldl (init + Imperative.Cmd.gotoInstrCount c) rest.
        -- Use foldl_eq_init_add (or move the initial value out).
        have h_cmd_count : Core.CmdExt.gotoInstrCount (Core.CmdExt.cmd c) =
            Imperative.Cmd.gotoInstrCount c := rfl
        -- We use Nat.add_comm and `List.foldl_assoc` if available; fall
        -- back to manual induction.
        have h_foldl_acc :
            ∀ (l : List Core.Command) (k : Nat),
              List.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) k l =
              k + List.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 l := by
          intro l
          induction l with
          | nil => simp
          | cons hd tl ih =>
            intro k
            simp only [List.foldl]
            rw [ih (k + Core.CmdExt.gotoInstrCount hd),
                ih (0 + Core.CmdExt.gotoInstrCount hd)]
            omega
        rw [show List.foldl
                  (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0
                  ((Core.CmdExt.cmd c) :: rest) =
              List.foldl
                  (fun acc c => acc + Core.CmdExt.gotoInstrCount c)
                  (0 + Imperative.Cmd.gotoInstrCount c) rest from rfl,
            h_foldl_acc rest (0 + Imperative.Cmd.gotoInstrCount c)]
        omega
      | .error e =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      unfold innerCmdLoop at h_run
      simp at h_run

/-! ## Monotonicity of `Cmd.toGotoInstructions` -/

/-- `Cmd.toGotoInstructions` only grows the instruction array. -/
theorem toGotoInstructions_size_le
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst]
      show trans.instructions.size ≤ (trans.instructions ++ #[_,_]).size
      rw [Array.size_append]; simp
    | nondet =>
      obtain ⟨_, _, _, _, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst, Array.size_push]; omega
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst, Array.size_push]; omega
    | nondet =>
      obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst, Array.size_push]; omega
  | assert label e md =>
    obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst, Array.size_push]; omega
  | assume label e md =>
    obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst, Array.size_push]; omega
  | cover label e md =>
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      rw [← h_run, Array.size_push]; omega
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- `Cmd.toGotoInstructions` preserves the input prefix on `?`-lookups:
any index `k < trans.instructions.size` reads the same in
`ans.instructions[k]?` as `trans.instructions[k]?`. (The `?`-lookup
form avoids the dependent-type elaboration issues that the
proof-style lookup hits.) -/
theorem toGotoInstructions_instructions_prefix?
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (k : Nat) (h_k : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_, _, i₀, i₁, _, _, _, _, _, _, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst]
      have h_eq : trans.instructions.append #[i₀, i₁] = trans.instructions ++ #[i₀, i₁] := rfl
      rw [h_eq, Array.getElem?_append_left h_k]
    | nondet =>
      obtain ⟨_, _, _, _, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
    | nondet =>
      obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
  | assert label e md =>
    obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
  | assume label e md =>
    obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
  | cover label e md =>
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      let assert_inst : CProverGOTO.Instruction :=
        { type := .ASSERT, locationNum := trans.nextLoc,
          sourceLoc := Imperative.metadataToSourceLoc md fname trans.sourceText
            (comment := md.getPropertySummary.getD s!"cover {label}"),
          guard := e_goto }
      have h_inst : ans.instructions = trans.instructions.push assert_inst := by
        rw [← h_run]
      rw [h_inst]
      rw [Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- `innerCmdLoop` only grows the instruction array. -/
theorem innerCmdLoop_size_le
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  induction cmds generalizing T trans with
  | nil =>
    rw [innerCmdLoop_nil] at h_run
    injection h_run with h_run
    rw [← h_run]; exact Nat.le_refl _
  | cons cmd rest ih =>
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        have := toGotoInstructions_size_le T fname c trans trans' h_step
        have := ih trans'.T trans' h_run
        omega
      | .error _ =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      unfold innerCmdLoop at h_run
      simp at h_run

/-- `innerCmdLoop` preserves the input prefix on `?`-lookups: any
index `k < trans.instructions.size` reads the same in
`ans.instructions[k]?` as `trans.instructions[k]?`. -/
theorem innerCmdLoop_instructions_prefix?
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans)
    (k : Nat) (h_k : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  induction cmds generalizing T trans with
  | nil =>
    rw [innerCmdLoop_nil] at h_run
    injection h_run with h_run
    subst h_run
    rfl
  | cons cmd rest ih =>
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        have h_k_trans' : k < trans'.instructions.size := by
          have := toGotoInstructions_size_le T fname c trans trans' h_step; omega
        rw [ih trans'.T trans' h_run h_k_trans']
        exact toGotoInstructions_instructions_prefix? T fname c trans trans' h_step k h_k
      | .error _ =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      unfold innerCmdLoop at h_run
      simp at h_run

/-! ## Per-block layout production

The layout_block_body theorem: each admitted `.cmd c` at position `k`
in `cmds` was emitted at offset `trans.nextLoc + cmdsPrefixInstrCount
cmds k`. We use a `pgm.instructions[i]?`-style prefix hypothesis (so
the proof avoids the dependent-type-rewrite issues of the
`?`-less form). -/

/-- Foldl-accumulator extraction: `foldl f k l = k + foldl f 0 l` for
the per-cmd instr-count function. Used in the offset calculations. -/
private theorem foldl_gotoInstrCount_extract_acc :
    ∀ (l : List Core.Command) (k : Nat),
      List.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) k l =
      k + List.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 l := by
  intro l
  induction l with
  | nil => simp
  | cons hd tl ih =>
    intro k
    simp only [List.foldl]
    rw [ih (k + Core.CmdExt.gotoInstrCount hd),
        ih (0 + Core.CmdExt.gotoInstrCount hd)]
    omega

/-- Per-Cmd nextLoc-advance: `Cmd.toGotoInstructions T fname c trans
= .ok ans` implies `ans.nextLoc = trans.nextLoc +
Imperative.Cmd.gotoInstrCount c`. -/
theorem toGotoInstructions_nextLoc_advance
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans) :
    ans.nextLoc = trans.nextLoc + Imperative.Cmd.gotoInstrCount c := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h_next, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_next]; rfl
    | nondet =>
      obtain ⟨_, _, _, _, _, _, _, h_next, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_next]; rfl
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, _, h_next⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_next]; rfl
    | nondet =>
      obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_next]; rfl
  | assert label e md =>
    obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_next]; rfl
  | assume label e md =>
    obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_next]; rfl
  | cover label e md =>
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      rw [← h_run]; rfl
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- The full per-block layout theorem: each admitted `.cmd c` at
position `k` in `cmds` was emitted at offset `trans.nextLoc +
cmdsPrefixInstrCount cmds k`. -/
theorem innerCmdLoop_layout_block_body
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_admitted :
      ∀ (k : Nat) (h : k < cmds.length),
        Core.CmdExt.isAdmittedCmd (cmds[k]'h) = true)
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    ∀ (k : Nat) (inner : Imperative.Cmd Core.Expression)
      (h : k < cmds.length),
      cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (trans.nextLoc + cmdsPrefixInstrCount cmds k) inner := by
  induction cmds generalizing T trans with
  | nil =>
    intro k inner h_lt _
    simp at h_lt
  | cons cmd rest ih =>
    intro k inner h_lt h_at
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        match k with
        | 0 =>
          -- Head case. h_at : (.cmd c) = .cmd inner, so after simp,
          -- h_at : c = inner.
          simp at h_at
          -- We substitute `inner` (the binding from `intro inner`) with
          -- `c` (the case-split variable). h_at says they're equal.
          rw [← h_at]
          -- Now goal mentions `c` in place of `inner`.
          have h_prefix0 : cmdsPrefixInstrCount (Core.CmdExt.cmd c :: rest) 0 = 0 :=
            rfl
          rw [h_prefix0, Nat.add_zero]
          -- Build h_prefix' for trans' from h_prefix on ans.
          have h_prefix' :
              ∀ (k : Nat) (h : k < trans'.instructions.size),
                pgm.instructions[k]? = some trans'.instructions[k] := by
            intro k h_k
            have h_size' : trans'.instructions.size = trans'.nextLoc :=
              toGotoInstructions_preserves_size_eq T fname c trans trans' h_step h_size
            have h_size_le_ans :
                trans'.instructions.size ≤ ans.instructions.size :=
              innerCmdLoop_size_le trans'.T fname rest trans' ans h_run
            have h_k_ans : k < ans.instructions.size := by omega
            have h_eq_q :
                ans.instructions[k]? = trans'.instructions[k]? :=
              innerCmdLoop_instructions_prefix? trans'.T fname rest trans' ans h_run k h_k
            rw [h_prefix k h_k_ans]
            rw [Array.getElem?_eq_getElem h_k_ans] at h_eq_q
            rw [Array.getElem?_eq_getElem h_k] at h_eq_q
            injection h_eq_q with h_eq_q
            rw [h_eq_q]
          have h_admitted0 := h_admitted 0 (by simp)
          exact cmdEmittedAt_of_toGotoInstructions
            T fname c h_admitted0 trans trans' h_step h_size
            pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq h_prefix'
        | k + 1 =>
          -- Tail case: recurse.
          have h_admitted' :
              ∀ (k' : Nat) (h : k' < rest.length),
                Core.CmdExt.isAdmittedCmd (rest[k']'h) = true := by
            intro k' h_k'
            have : k' + 1 < (Core.CmdExt.cmd c :: rest).length := by
              show Nat.succ k' < Nat.succ rest.length
              exact Nat.succ_lt_succ h_k'
            have := h_admitted (k' + 1) this
            simpa using this
          have h_lt_rest : k < rest.length := by
            simp at h_lt
            exact Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ h_lt)
          have h_at_rest : rest[k]'h_lt_rest = .cmd inner := by
            have := h_at
            simp at this
            exact this
          have h_size' : trans'.instructions.size = trans'.nextLoc :=
            toGotoInstructions_preserves_size_eq T fname c trans trans' h_step h_size
          have h_advance :
              trans'.nextLoc = trans.nextLoc + Imperative.Cmd.gotoInstrCount c :=
            toGotoInstructions_nextLoc_advance T fname c trans trans' h_step
          have h_ih := ih trans'.T trans' h_run h_size' h_admitted' k inner h_lt_rest h_at_rest
          -- Adjust the offset.
          have h_offset_eq :
              trans'.nextLoc + cmdsPrefixInstrCount rest k =
              trans.nextLoc + cmdsPrefixInstrCount (Core.CmdExt.cmd c :: rest) (k + 1) := by
            rw [h_advance]
            -- cmdsPrefixInstrCount (cmd c :: rest) (k+1)
            --   = ((cmd c :: rest).take (k+1)).foldl ...
            --   = (cmd c :: rest.take k).foldl ...
            -- via List.take_succ_cons.
            simp only [cmdsPrefixInstrCount, List.take_succ_cons, List.foldl]
            -- Apply foldl-acc-extraction lemma to factor out the initial
            -- accumulator.
            rw [foldl_gotoInstrCount_extract_acc (rest.take k)
                (0 + Core.CmdExt.gotoInstrCount (Core.CmdExt.cmd c))]
            -- Both sides have foldl 0 (rest.take k) plus various
            -- Imperative.Cmd.gotoInstrCount c terms.
            -- Core.CmdExt.gotoInstrCount (.cmd c) = Imperative.Cmd.gotoInstrCount c.
            show trans.nextLoc + Imperative.Cmd.gotoInstrCount c +
                cmdsPrefixInstrCount rest k =
              trans.nextLoc + (0 + Core.CmdExt.gotoInstrCount (Core.CmdExt.cmd c) +
                List.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 (rest.take k))
            simp [cmdsPrefixInstrCount, Core.CmdExt.gotoInstrCount]
            omega
          rw [h_offset_eq] at h_ih
          exact h_ih
      | .error _ =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      have h_contra := h_admitted 0 (by simp)
      simp [Core.CmdExt.isAdmittedCmd] at h_contra

/-! ## LabelMap operations and invariants

The translator threads a `Std.HashMap String Nat` for `labelMap`,
inserting `label ↦ trans.nextLoc` at the start of each outer-loop
iteration. We model the labelMap as a `LabelMap = String → Option Nat`
function, which is the form `WellFormedTranslation` consumes.

The key operation: extending an existing `labelMap` with `label ↦ pc`.
This only preserves injectivity when `label` is fresh (not already in
the map's domain), which corresponds to the implicit
`BlockLabelsDistinct cfg` requirement on the input CFG. -/

/-- Extend a `LabelMap` with one new `label ↦ pc` mapping. -/
@[expose] def labelMapInsert
    (m : LabelMap) (label : String) (pc : Nat) : LabelMap :=
  fun l => if l = label then some pc else m l

/-- Inserting a fresh label preserves injectivity, provided the new
`pc` is also fresh (not already in the codomain of `m`). -/
theorem labelMapInsert_preserves_inj
    (m : LabelMap) (label : String) (pc : Nat)
    (h_inj :
      ∀ l₁ l₂ pc', m l₁ = some pc' → m l₂ = some pc' → l₁ = l₂)
    (h_fresh_dom : m label = none)
    (h_fresh_cod : ∀ l pc', m l = some pc' → pc' ≠ pc) :
    ∀ l₁ l₂ pc', (labelMapInsert m label pc) l₁ = some pc' →
      (labelMapInsert m label pc) l₂ = some pc' →
      l₁ = l₂ := by
  intro l₁ l₂ pc' h₁ h₂
  unfold labelMapInsert at h₁ h₂
  by_cases hl₁ : l₁ = label
  · by_cases hl₂ : l₂ = label
    · rw [hl₁, hl₂]
    · -- l₁ = label, l₂ ≠ label.
      -- h₁ says some pc = some pc', so pc' = pc.
      simp [hl₁] at h₁
      simp [hl₂] at h₂
      -- But m l₂ = some pc' and pc' = pc, contradicting h_fresh_cod.
      subst h₁
      have := h_fresh_cod l₂ pc h₂
      contradiction
  · by_cases hl₂ : l₂ = label
    · -- Symmetric to above.
      simp [hl₁] at h₁
      simp [hl₂] at h₂
      subst h₂
      have := h_fresh_cod l₁ pc h₁
      contradiction
    · -- Neither is `label`; both lookups go to `m`.
      simp [hl₁] at h₁
      simp [hl₂] at h₂
      exact h_inj l₁ l₂ pc' h₁ h₂

/-- Inserting a label preserves the `pc < nextLoc` bound provided the
new `pc` is also `< nextLoc`. -/
theorem labelMapInsert_preserves_lt
    (m : LabelMap) (label : String) (pc : Nat) (nextLoc : Nat)
    (h_lt_old : ∀ l pc', m l = some pc' → pc' < nextLoc)
    (h_pc_lt : pc < nextLoc) :
    ∀ l pc', (labelMapInsert m label pc) l = some pc' → pc' < nextLoc := by
  intro l pc' h
  unfold labelMapInsert at h
  by_cases h_eq : l = label
  · simp [h_eq] at h
    rw [← h]; exact h_pc_lt
  · simp [h_eq] at h
    exact h_lt_old l pc' h

/-- After `labelMapInsert`, the inserted label resolves to its `pc`. -/
@[simp] theorem labelMapInsert_self
    (m : LabelMap) (label : String) (pc : Nat) :
    (labelMapInsert m label pc) label = some pc := by
  unfold labelMapInsert
  simp

/-- After `labelMapInsert`, an unrelated label resolves the same as in
the original map. -/
@[simp] theorem labelMapInsert_other
    (m : LabelMap) (label l : String) (pc : Nat) (h : l ≠ label) :
    (labelMapInsert m label pc) l = m l := by
  unfold labelMapInsert
  simp [h]

/-- Convert a `Std.HashMap String Nat` to a `LabelMap = String →
Option Nat` via `m.get?`. The translator's `CoreCFGTransLoopState`
threads a `HashMap`; the `WellFormedTranslation` consumer expects a
function form. -/
@[expose] def hashMapToLabelMap (m : Std.HashMap String Nat) : LabelMap :=
  fun l => m[l]?

/-- The empty hashmap converts to `emptyLabelMap`. -/
@[simp] theorem hashMapToLabelMap_empty :
    hashMapToLabelMap (∅ : Std.HashMap String Nat) = emptyLabelMap := by
  funext l
  unfold hashMapToLabelMap emptyLabelMap
  simp

/-- Conversion of an inserted hashmap pulls the inserted entry out and
falls through to the underlying map. We use the underlying-LabelMap
function `labelMapInsert` to model this. -/
theorem hashMapToLabelMap_insert
    (m : Std.HashMap String Nat) (label : String) (pc : Nat) :
    hashMapToLabelMap (m.insert label pc) =
      labelMapInsert (hashMapToLabelMap m) label pc := by
  funext l
  unfold hashMapToLabelMap labelMapInsert
  rw [Std.HashMap.getElem?_insert]
  by_cases h : l = label
  · subst h
    simp
  · have h' : ¬ label = l := fun h' => h h'.symm
    simp [h, h']

/-! ## Per-cmd / per-block step preservation (refactor-aware)

After the round-3 refactor of `coreCFGToGotoTransform`, the translator
is structured as

```
cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) initSt
  >>= λ st => st.pendingPatches.foldlM (Strata.coreCFGToGotoPatchStep ..) ([], st.trans)
  >>= λ (resolved, trans) => Imperative.patchGotoTargets trans resolved
```

with named per-cmd / per-block / per-patch step functions. The
preservation lemmas below characterise each step's effect on the
partial `WellFormedTranslation` invariant. -/

/-- The per-cmd step `Strata.coreCFGToGotoCmdStep` agrees with
`Cmd.toGotoInstructions` on the `.cmd c` case, and produces a single
appended FUNCTION_CALL instruction on the `.call` case. -/
theorem coreCFGToGotoCmdStep_cmd
    (fname : String) (c : Imperative.Cmd Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    Strata.coreCFGToGotoCmdStep fname trans (.cmd c) =
      Imperative.Cmd.toGotoInstructions trans.T fname c trans := by
  unfold Strata.coreCFGToGotoCmdStep
  rfl

/-- The per-cmd step preserves `instructions.size = nextLoc` on
admitted commands (i.e., `.cmd c`; `.call` is rejected by
`isAdmittedCmd`). -/
theorem coreCFGToGotoCmdStep_preserves_size_eq
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_size_eq trans.T fname c trans ans h_run h_size
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The per-cmd step preserves `locationNum = index` on admitted
commands. -/
theorem coreCFGToGotoCmdStep_preserves_locationNum_eq_index
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_locationNum_eq_index
      trans.T fname c trans ans h_run h_size h_loc
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold via `foldlM` preserves `size_eq`, when each cmd is
admitted by `isAdmittedCmd`. -/
theorem cmdsFoldlM_preserves_size_eq
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size' : trans'.instructions.size = trans'.nextLoc :=
        coreCFGToGotoCmdStep_preserves_size_eq fname cmd trans trans'
          h_admitted_cmd h_step h_size
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      exact ih trans' h_admitted_rest h_run h_size'
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The cmds-fold via `foldlM` preserves `locationNum_eq_index`. -/
theorem cmdsFoldlM_preserves_locationNum_eq_index
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size' : trans'.instructions.size = trans'.nextLoc :=
        coreCFGToGotoCmdStep_preserves_size_eq fname cmd trans trans'
          h_admitted_cmd h_step h_size
      have h_loc' :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            trans'.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoCmdStep_preserves_locationNum_eq_index
          fname cmd trans trans' h_admitted_cmd h_step h_size h_loc
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      exact ih trans' h_admitted_rest h_run h_size' h_loc'
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The per-cmd step's `nextLoc` advance equals `Core.CmdExt.gotoInstrCount cmd`. -/
theorem coreCFGToGotoCmdStep_nextLoc_advance
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans) :
    ans.nextLoc = trans.nextLoc + Core.CmdExt.gotoInstrCount cmd := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    have := toGotoInstructions_nextLoc_advance trans.T fname c trans ans h_run
    rw [this]
    rfl
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold's `nextLoc` advance equals `DetBlockBodyInstrCount`
applied to a synthetic block. -/
theorem cmdsFoldlM_nextLoc_advance
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans) :
    ans.nextLoc =
      trans.nextLoc + cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; simp
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_advance' : trans'.nextLoc = trans.nextLoc + Core.CmdExt.gotoInstrCount cmd :=
        coreCFGToGotoCmdStep_nextLoc_advance fname cmd trans trans' h_admitted_cmd h_step
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have h_ih := ih trans' h_admitted_rest h_run
      rw [h_ih, h_advance']
      -- Goal: trans.nextLoc + gotoInstrCount cmd + foldl (+) 0 rest =
      --        trans.nextLoc + foldl (+) 0 (cmd :: rest)
      simp only [List.foldl]
      rw [foldl_gotoInstrCount_extract_acc rest (0 + Core.CmdExt.gotoInstrCount cmd)]
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Per-block step preservation

The per-block step's body is a sequence of three pieces: `emitLabel`,
`block.cmds.foldlM coreCFGToGotoCmdStep`, and the transfer-emit branch
(condGoto or finish). The lemmas below establish that this composition
preserves `size_eq` and `locationNum_eq_index`. -/

/-- The per-block step preserves `size_eq` (admitted cmds only). -/
theorem coreCFGToGotoBlockStep_preserves_size_eq
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    st'.trans.instructions.size = st'.trans.nextLoc := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Step 1: emitLabel produces a state with size_eq.
  have h_size₁ :
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).instructions.size =
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).nextLoc :=
    emitLabel_preserves_size_eq label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size
  -- Unfold the step function and the inner do-block.
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  -- Now `h_run` has shape `match (foldlM ...) with .ok x => match transfer with ... | .error => Except.error _`.
  -- Case on the inner-fold result.
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_size₂ : trans₂.instructions.size = trans₂.nextLoc :=
      cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁
    -- h_run now is `(match transfer ...) = Except.ok st'`. Case on transfer.
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, h_cond_eval =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push, h_size₂]
      | .error e, h_cond_eval =>
        simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp [Array.size_push, h_size₂]
  | .error e, h_inner =>
    simp at h_run

/-- The per-block step preserves `locationNum_eq_index`. -/
theorem coreCFGToGotoBlockStep_preserves_locationNum_eq_index
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st.trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      st'.trans.instructions[i]? = some instr → instr.locationNum = i := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Step 1: emitLabel preserves size_eq + locationNum_eq_index.
  have h_size₁ :
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).instructions.size =
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).nextLoc :=
    emitLabel_preserves_size_eq label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size
  have h_loc₁ :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[i]? = some instr → instr.locationNum = i :=
    emitLabel_preserves_locationNum_eq_index label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size h_loc
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_size₂ : trans₂.instructions.size = trans₂.nextLoc :=
      cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁
    have h_loc₂ :
        ∀ (i : Nat) (instr : CProverGOTO.Instruction),
          trans₂.instructions[i]? = some instr → instr.locationNum = i :=
      cmdsFoldlM_preserves_locationNum_eq_index fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁ h_loc₁
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, h_cond_eval =>
        simp only at h_run
        injection h_run with h_run
        intro i instr h
        rw [← h_run] at h
        -- After two emitGoto pushes, the array has 2 more instructions.
        -- Use emitCondGoto / emitUncondGoto preservation lemmas.
        have h_after_neg :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              trans₂).fst.instructions[i]? = some instr → instr.locationNum = i :=
          emitCondGoto_preserves_locationNum_eq_index
            (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_size₂ h_loc₂
        have h_after_neg_size :
          (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            trans₂).fst.instructions.size =
          (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            trans₂).fst.nextLoc :=
          emitCondGoto_preserves_size_eq
            (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_size₂
        have h_after_uncond :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            (Imperative.emitUncondGoto
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
                (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
                trans₂).fst).fst.instructions[i]? = some instr →
            instr.locationNum = i :=
          emitUncondGoto_preserves_locationNum_eq_index
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            _ h_after_neg_size h_after_neg
        exact h_after_uncond i instr h
      | .error e, h_cond_eval =>
        simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      intro i instr h
      rw [← h_run] at h
      -- After pushing 1 END_FUNCTION, locationNum_eq_index transfers via
      -- a generic push lemma.
      exact endFunction_emit_preserves_locationNum_eq_index md fname trans₂ h_size₂ h_loc₂ i instr h
  | .error e, h_inner =>
    simp at h_run

/-! ### Per-block step layout effects

The per-block step's effect on `st`'s fields:
* `st'.labelMap = st.labelMap.insert lblBlk.1 st.trans.nextLoc`
* `st'.trans.nextLoc = st.trans.nextLoc + 1 + bodyCount + transferCount`
* The block's pc (= `st.trans.nextLoc`) addresses a LOCATION instruction
  in `st'.trans.instructions` (the leading `emitLabel` push).
* For `.finish md`: position `pc + 1 + bodyCount` holds an END_FUNCTION.
* For `.condGoto cond lt lf md`: positions `pc + 1 + bodyCount` and
  `pc + 1 + bodyCount + 1` hold two GOTOs (target = none, guard =
  `e_goto.not` and `Expr.true` respectively).
* The pendingPatches array is extended by two patches for `.condGoto`
  blocks; preserved for `.finish` blocks. -/

/-- The per-block step's effect on `st.labelMap` is to insert
`lblBlk.1 ↦ st.trans.nextLoc`. -/
theorem coreCFGToGotoBlockStep_labelMap
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.labelMap = st.labelMap.insert lblBlk.1 st.trans.nextLoc := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, _ =>
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
  | .error _, _ => simp at h_run

/-- The per-block step's effect on `st.trans.nextLoc` for `.finish md`
blocks: it advances by `1 + bodyCount + 1` (the trailing `+1` is the
END_FUNCTION push). -/
theorem coreCFGToGotoBlockStep_nextLoc_advance_finish
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .finish md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.trans.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 1 := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_advance₂ :
        trans₂.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk := by
      have := cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc =
          st.trans.nextLoc + 1 := rfl
      rw [h_after_label] at this
      rw [this]
      simp [DetBlockBodyInstrCount]
    rw [h_transfer] at h_run
    simp only at h_run
    injection h_run with h_run
    rw [← h_run]
    show trans₂.nextLoc + 1 = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1
    omega
  | .error _, _ => simp at h_run

/-- The per-block step's effect on `st.trans.nextLoc` for `.condGoto`
blocks: it advances by `1 + bodyCount + 2`. -/
theorem coreCFGToGotoBlockStep_nextLoc_advance_condGoto
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (cond : Core.Expression.Expr) (lt lf : String)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .condGoto cond lt lf md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.trans.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 2 := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_advance₂ :
        trans₂.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk := by
      have := cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc =
          st.trans.nextLoc + 1 := rfl
      rw [h_after_label] at this
      rw [this]
      simp [DetBlockBodyInstrCount]
    rw [h_transfer] at h_run
    simp only at h_run
    generalize h_cond_eval :
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
    match cond_eval, h_cond_eval with
    | .ok cond_expr, _ =>
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
      omega
    | .error _, _ => simp at h_run
  | .error _, _ => simp at h_run

/-! ### Per-block step instruction-array prefix preservation

The per-block step only appends to `trans.instructions`. This means
positions `[0, st.trans.instructions.size)` keep the same instruction
through the block step. Composed with foldlM, this gives positions
`[0, st_initial.trans.instructions.size)` retaining their original
contents through all blocks. -/

/-- Each step in `cmdsFoldlM` only grows the instruction array. -/
theorem coreCFGToGotoCmdStep_size_le
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_size_le trans.T fname c trans ans h_run
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- Each step in `cmdsFoldlM` preserves the instruction-array prefix
on `?`-lookups. -/
theorem coreCFGToGotoCmdStep_instructions_prefix?
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (k : Nat) (h : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_instructions_prefix? trans.T fname c trans ans h_run k h
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold preserves the instruction-array prefix on
`?`-lookups: any index `k` below the input size returns the same
instruction in `ans` as in `trans`. -/
theorem cmdsFoldlM_instructions_prefix?
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (k : Nat) (h : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size_le : trans.instructions.size ≤ trans'.instructions.size :=
        coreCFGToGotoCmdStep_size_le fname cmd trans trans' h_admitted_cmd h_step
      have h_k' : k < trans'.instructions.size := Nat.lt_of_lt_of_le h h_size_le
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have h_ih := ih trans' h_admitted_rest h_run h_k'
      rw [h_ih]
      exact coreCFGToGotoCmdStep_instructions_prefix? fname cmd trans trans' h_admitted_cmd h_step k h
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- `cmdsFoldlM_size_le` — the cmds-fold only grows the instruction
array. -/
theorem cmdsFoldlM_size_le
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact Nat.le_refl _
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_le := coreCFGToGotoCmdStep_size_le fname cmd trans trans' h_admitted_cmd h_step
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have := ih trans' h_admitted_rest h_run
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The per-block step only grows the instruction array. -/
theorem coreCFGToGotoBlockStep_size_le
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st.trans.instructions.size ≤ st'.trans.instructions.size := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_le :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size ≤ trans₂.instructions.size :=
      cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push]
        omega
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp [Array.size_push]
      omega
  | .error _, _ => simp at h_run

/-- The per-block step preserves the instruction-array prefix on
`?`-lookups: any index `k` below the input size returns the same
instruction in `st'.trans` as in `st.trans`. -/
theorem coreCFGToGotoBlockStep_instructions_prefix?
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (k : Nat) (h : k < st.trans.instructions.size) :
    st'.trans.instructions[k]? = st.trans.instructions[k]? := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- emitLabel(...).instructions = st.trans.instructions.push <new>
    have h_label_unfold :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions =
        st.trans.instructions.push
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := rfl
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      rw [h_label_unfold, Array.size_push]
    have h_k_after_label :
        k < (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size := by
      rw [h_label_size]; omega
    have h_label_lookup :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[k]? = st.trans.instructions[k]? := by
      rw [h_label_unfold]
      rw [Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]
    have h_inner_prefix :
        trans₂.instructions[k]? =
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[k]? :=
      cmdsFoldlM_instructions_prefix? fname blk.cmds _ trans₂ h_admitted h_inner k h_k_after_label
    have h_inner_size_le :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size ≤ trans₂.instructions.size :=
      cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        have h_k_in_trans₂ : k < trans₂.instructions.size := by omega
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        have h_k_in_post_first :
            k < (trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc, target := .none }).size := by
          simp [Array.size_push]; omega
        rw [Array.getElem?_push_lt h_k_in_post_first,
            Array.getElem_push_lt h_k_in_trans₂,
            ← Array.getElem?_eq_getElem h_k_in_trans₂]
        rw [h_inner_prefix, h_label_lookup]
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      have h_k_in_trans₂ : k < trans₂.instructions.size := by omega
      rw [Array.getElem?_push_lt h_k_in_trans₂,
          ← Array.getElem?_eq_getElem h_k_in_trans₂]
      rw [h_inner_prefix, h_label_lookup]
  | .error _, _ => simp at h_run

/-! ### Per-block step layout post-conditions

After one block step, certain instructions are at specific positions in
`st'.trans.instructions`:

* The LOCATION instruction is at `st.trans.nextLoc`.
* For `.finish md` blocks: the END_FUNCTION is at `st.trans.nextLoc + 1
  + bodyCount`.
* For `.condGoto cond lt lf md` blocks: two GOTOs at `st.trans.nextLoc
  + 1 + bodyCount` (guard `e_goto.not`, target `none`) and at `+1`
  (guard `Expr.true`, target `none`).

These results are stable through subsequent block steps because of
`coreCFGToGotoBlockStep_instructions_prefix?`. -/

/-- After one block step, the LOCATION instruction is at
`st.trans.nextLoc` in `st'.trans.instructions`. -/
theorem coreCFGToGotoBlockStep_location_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr,
      st'.trans.instructions[st.trans.nextLoc]? = some instr ∧
      instr.type = .LOCATION := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- The LOCATION instruction is the LAST one pushed by emitLabel.
    have h_label_unfold :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions =
        st.trans.instructions.push
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := rfl
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      rw [h_label_unfold, Array.size_push]
    have h_label_at :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [h_label_unfold, Array.getElem?_push_eq]
    -- Show that the inner cmds-fold preserves this LOCATION.
    have h_pc_lt : st.trans.instructions.size <
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size := by
      rw [h_label_size]; omega
    have h_pc_in_trans₂ :
        trans₂.instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [cmdsFoldlM_instructions_prefix? fname blk.cmds _ trans₂ h_admitted h_inner _ h_pc_lt]
      exact h_label_at
    -- pc = st.trans.nextLoc = st.trans.instructions.size by h_size.
    have h_pc_eq : st.trans.nextLoc = st.trans.instructions.size := h_size.symm
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        rw [h_pc_eq]
        have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
          have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
          rw [h_label_size] at this; omega
        have h_pc_in_first :
            st.trans.instructions.size < (trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc, target := .none }).size := by
          simp [Array.size_push]; omega
        rw [Array.getElem?_push_lt h_pc_in_first,
            Array.getElem_push_lt h_pc_in_trans₂_size,
            ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
        rw [h_pc_in_trans₂]
        exact ⟨_, rfl, rfl⟩
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      rw [h_pc_eq]
      have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
        have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
        rw [h_label_size] at this; omega
      rw [Array.getElem?_push_lt h_pc_in_trans₂_size,
          ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
      rw [h_pc_in_trans₂]
      exact ⟨_, rfl, rfl⟩
  | .error _, _ => simp at h_run

/-- After one block step on a `.finish md` block, the END_FUNCTION
instruction is at `st.trans.nextLoc + 1 + bodyCount` in
`st'.trans.instructions`. -/
theorem coreCFGToGotoBlockStep_finish_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .finish md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr,
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2]? = some instr ∧
      instr.type = .END_FUNCTION := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    rw [h_transfer] at h_run
    simp only at h_run
    injection h_run with h_run
    rw [← h_run]
    -- After the END_FUNCTION push, position trans₂.instructions.size = pc + 1 + bodyCount
    -- holds the new END_FUNCTION instruction.
    have h_target_eq :
        st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk = trans₂.instructions.size := by
      rw [h_inner_size]; omega
    rw [h_target_eq]
    refine ⟨{ type := .END_FUNCTION, locationNum := trans₂.nextLoc,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText }, ?_, rfl⟩
    show (trans₂.instructions.push _)[trans₂.instructions.size]? = some _
    exact Array.getElem?_push_size
  | .error _, _ => simp at h_run

/-- After one block step on a `.condGoto cond lt lf md` block, two GOTO
instructions appear at `st.trans.nextLoc + 1 + bodyCount` (guard
`e_goto.not`, target `none`) and at `+1` (guard `Expr.true`, target
`none`). -/
theorem coreCFGToGotoBlockStep_condGoto_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (cond : Core.Expression.Expr) (lt lf : String)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .condGoto cond lt lf md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr_neg instr_uncond e_goto,
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2]? = some instr_neg ∧
      instr_neg.type = .GOTO ∧
      instr_neg.target = none ∧
      instr_neg.guard = e_goto.not ∧
      Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = .ok e_goto ∧
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 1]? = some instr_uncond ∧
      instr_uncond.type = .GOTO ∧
      instr_uncond.target = none ∧
      instr_uncond.guard = CProverGOTO.Expr.true := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    rw [h_transfer] at h_run
    simp only at h_run
    -- Use generalize-with-equation style to keep h_eq usable.
    -- We must `revert h_run` to expose the type containing the LHS of the cond_eval.
    revert h_run
    generalize h_eq :
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = res
    intro h_run
    -- Capture h_eq into the existential pre-emptively.
    -- Re-state h_eq before the cases analysis (so it's not over a substituted res).
    cases res with
    | error _ => simp at h_run
    | ok cond_expr =>
      -- Now h_eq : ... = Except.ok cond_expr.
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      have h_pc_neg_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk = trans₂.instructions.size := by
        rw [h_inner_size]; omega
      have h_pc_uncond_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1 = trans₂.instructions.size + 1 := by
        rw [h_inner_size]; omega
      simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
      have h_neg :
          ((trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc }).push
            { type := .GOTO, guard := CProverGOTO.Expr.true,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
              locationNum := trans₂.nextLoc + 1 })[trans₂.instructions.size]?
          = some
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc } := by
        rw [Array.getElem?_push_lt (by simp [Array.size_push])]
        congr 1
        exact Array.getElem_push_eq
      -- For h_uncond, use the fact that pushing onto an array of size n+1 makes
      -- the new last element accessible via getElem? at index n+1.
      -- We use `Array.getElem?_push_size` after rewriting.
      have h_uncond :
          ((trans₂.instructions.push
              ({ type := .GOTO, guard := cond_expr.not,
                 sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                 locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)).push
            { type := .GOTO, guard := CProverGOTO.Expr.true,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
              locationNum := trans₂.nextLoc + 1 })[trans₂.instructions.size + 1]?
          = some
              { type := .GOTO, guard := CProverGOTO.Expr.true,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc + 1 } := by
        let arr1 := trans₂.instructions.push
            ({ type := .GOTO, guard := cond_expr.not,
               sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
               locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)
        have h_size_inner : arr1.size = trans₂.instructions.size + 1 := by
          simp [arr1, Array.size_push]
        show (arr1.push _)[trans₂.instructions.size + 1]? = _
        rw [← h_size_inner]
        exact Array.getElem?_push_size
      refine ⟨_, _, cond_expr, by rw [h_pc_neg_eq]; exact h_neg, rfl, rfl, rfl, ?_,
        by rw [h_pc_uncond_eq]; exact h_uncond, rfl, rfl, rfl⟩
      -- h_eq has the form `Lambda.LExpr.toGotoExprCtx [] cond = Except.ok cond_expr`,
      -- but simp may have already substituted in the goal; either way, rfl or h_eq
      -- works.
      first | rfl | exact h_eq
  | .error _, _ => simp at h_run

/-- The outer-loop fold preserves `size_eq` if every block's body is
admitted. -/
theorem blocksFoldlM_preserves_size_eq
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    st'.trans.instructions.size = st'.trans.nextLoc := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname head st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The outer-loop fold preserves `locationNum_eq_index`. -/
theorem blocksFoldlM_preserves_locationNum_eq_index
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st.trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      st'.trans.instructions[i]? = some instr → instr.locationNum = i := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname head st st₁ h_admitted_head h_step h_size
      have h_loc₁ :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            st₁.trans.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoBlockStep_preserves_locationNum_eq_index fname head st st₁
          h_admitted_head h_step h_size h_loc
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁ h_loc₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Outer-loop foldlM layout-fact preservation

The per-block layout facts (LOCATION at pc, END_FUNCTION/condGoto-pair
at the end of the block) need to be propagated through subsequent
block iterations using `coreCFGToGotoBlockStep_instructions_prefix?`.

The labelMap accumulates entries for each processed block; we need
that distinct block labels stay distinct in the final HashMap. -/

/-- The outer foldlM only grows the instruction array. -/
theorem blocksFoldlM_size_le
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st') :
    st.trans.instructions.size ≤ st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact Nat.le_refl _
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_le := coreCFGToGotoBlockStep_size_le fname head st st₁ h_admitted_head h_step
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have := ih st₁ h_admitted_rest h_run
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The outer foldlM preserves the instruction-array prefix. -/
theorem blocksFoldlM_instructions_prefix?
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (k : Nat) (h : k < st.trans.instructions.size) :
    st'.trans.instructions[k]? = st.trans.instructions[k]? := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_le := coreCFGToGotoBlockStep_size_le fname head st st₁ h_admitted_head h_step
      have h_k₁ : k < st₁.trans.instructions.size := Nat.lt_of_lt_of_le h h_le
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_ih := ih st₁ h_admitted_rest h_run h_k₁
      rw [h_ih]
      exact coreCFGToGotoBlockStep_instructions_prefix? fname head st st₁ h_admitted_head h_step k h
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Layout-fact propagation through foldlM

For each `(l, blk)` in the processed prefix, we want the LOCATION,
END_FUNCTION, or condGoto-pair of that block to remain in the final
`st_final.trans.instructions` array at the same offset. The position
of the block (the snapshot of `nextLoc` at the start of the block's
iteration) is captured by walking the foldlM with an accumulator.

The labelMap accumulates entries — block `i` inserts `(label_i ↦
pc_i)`. Subsequent iterations may overwrite if `label_j = label_i` for
`j > i`. To ensure the labelMap-correspondence works, we require
distinct labels (`BlockLabelsDistinct`).

These lemmas thread a `BlockLabelsDistinct` hypothesis: the labels of
all blocks in `blocks` are pairwise distinct. -/

/-- A list of blocks has pairwise distinct labels. -/
@[expose] def BlockLabelsDistinct
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression)) :
    Prop :=
  List.Pairwise (fun a b => a.1 ≠ b.1) blocks

/-- A `Pairwise` distinctness on labels implies any element's label is
distinct from all subsequent labels. -/
theorem BlockLabelsDistinct_head_neq_tail
    (head : String × Imperative.DetBlock String Core.Command Core.Expression)
    (rest : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (h : BlockLabelsDistinct (head :: rest)) :
    ∀ p ∈ rest, head.1 ≠ p.1 := by
  unfold BlockLabelsDistinct at h
  cases h with
  | cons h_head h_rest =>
    intro p h_in
    exact h_head p h_in

/-- A `Pairwise` distinctness on the tail. -/
theorem BlockLabelsDistinct_tail
    (head : String × Imperative.DetBlock String Core.Command Core.Expression)
    (rest : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (h : BlockLabelsDistinct (head :: rest)) :
    BlockLabelsDistinct rest := by
  unfold BlockLabelsDistinct at h ⊢
  cases h with
  | cons _ h_rest => exact h_rest

/-- After the foldlM, if a label is in the labelMap of the input
state, it remains the same in the output state — provided the label is
not the head of any block in the processed list (because each block's
step only inserts its own label). -/
theorem blocksFoldlM_labelMap_preserves_external
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (l : String) (h_not_in : ∀ p ∈ blocks, p.1 ≠ l) :
    st'.labelMap[l]? = st.labelMap[l]? := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_lbl₁ : st₁.labelMap = st.labelMap.insert head.1 st.trans.nextLoc :=
        coreCFGToGotoBlockStep_labelMap fname head st st₁ h_step
      have h_not_l_head : head.1 ≠ l := h_not_in head (by simp)
      have h_not_l_rest : ∀ p ∈ rest, p.1 ≠ l := fun p hp => h_not_in p (by simp [hp])
      have h_ih := ih st₁ h_admitted_rest h_run h_not_l_rest
      rw [h_ih, h_lbl₁]
      rw [Std.HashMap.getElem?_insert]
      have h_l_neq : ¬ head.1 = l := h_not_l_head
      simp [h_l_neq]
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- For each `(l, blk) ∈ blocks` such that the foldlM produces
`st_final`, there exists a `pc` with:
* `st_final.labelMap[l]? = some pc`
* `st_final.trans.instructions[pc]? = some instr` and `instr.type = .LOCATION`
* `pc < st_final.trans.instructions.size`

The proof works by induction on `blocks`. -/
theorem blocksFoldlM_layout_location
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk, (l, blk) ∈ blocks →
      ∃ pc instr,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc]? = some instr ∧
        instr.type = .LOCATION ∧
        pc < st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    intro l blk h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk h_in
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_distinct_rest : BlockLabelsDistinct rest := BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st₁ : st.trans.instructions.size ≤ st₁.trans.instructions.size :=
        coreCFGToGotoBlockStep_size_le fname hd st st₁ h_admitted_head h_step
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      -- Either (l, blk) = hd, or (l, blk) ∈ rest.
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · -- (l, blk) = hd.
        subst h_eq
        obtain ⟨instr, h_at_st₁, h_ty⟩ :=
          coreCFGToGotoBlockStep_location_at_pc fname (l, blk) st st₁ h_admitted_head h_step h_size
        have h_pc_lt_st₁ : st.trans.nextLoc < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_st₁
          exact h_at_st₁.1
        have h_pc_lt_st' : st.trans.nextLoc < st'.trans.instructions.size :=
          Nat.lt_of_lt_of_le h_pc_lt_st₁ h_le_st'
        have h_at_st' : st'.trans.instructions[st.trans.nextLoc]? = some instr := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_lt_st₁]
          exact h_at_st₁
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? := by
          exact blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        refine ⟨st.trans.nextLoc, instr, h_lbl_st', h_at_st', h_ty, h_pc_lt_st'⟩
      · -- (l, blk) ∈ rest. Apply IH.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- For each `(l, blk) ∈ blocks` such that `blk.transfer = .finish md`,
the foldlM puts an END_FUNCTION at `pc + 1 + bodyCount` for the
appropriate pc. -/
theorem blocksFoldlM_layout_finish
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk md, (l, blk) ∈ blocks → blk.transfer = .finish md →
      ∃ pc instr_end,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_end ∧
        instr_end.type = .END_FUNCTION := by
  induction blocks generalizing st with
  | nil =>
    intro l blk md h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk md h_in h_transfer
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_distinct_rest : BlockLabelsDistinct rest := BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · subst h_eq
        -- (l, blk) is the head; transfer is .finish md.
        obtain ⟨instr_end, h_at_st₁, h_ty⟩ :=
          coreCFGToGotoBlockStep_finish_at_pc fname (l, blk) st st₁ md h_transfer h_admitted_head h_step h_size
        -- Propagate through the rest of the foldlM.
        have h_pc_lt_st₁ : st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_st₁
          exact h_at_st₁.1
        have h_at_st' :
            st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk]? =
              some instr_end := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_lt_st₁]
          exact h_at_st₁
        -- Now show st'.labelMap[l]? = some st.trans.nextLoc.
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? :=
          blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        refine ⟨st.trans.nextLoc, instr_end, h_lbl_st', h_at_st', h_ty⟩
      · -- Apply IH on rest.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk md h_in_rest h_transfer
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patch-step preservation (under empty loopContracts)

The patch step (`coreCFGToGotoPatchStep`) either fails (label
unresolved), prepends `(idx, targetLoc)` to `resolvedPatches`, or also
mutates `trans.instructions[idx].guard` for loop contracts. Reasoning
about the loop-contract guard tweak requires loop-contract-specific
infrastructure beyond Gap A. We discharge the patch step under the
hypothesis `loopContracts = ∅`, which is the case for any CFG without
loop-invariant or loop-decreases metadata; concrete callers verifying
the WF property pass this hypothesis. -/

/-- When `loopContracts` is empty, the patch step returns the input
`trans` unchanged (only modifies `resolvedPatches`). -/
theorem coreCFGToGotoPatchStep_no_contracts_trans_eq
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc') :
    acc'.2 = acc.2 := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  unfold Strata.coreCFGToGotoPatchStep at h_run
  simp only [Bind.bind, Except.bind] at h_run
  cases h_lookup : labelMap[label]? with
  | none =>
    rw [h_lookup] at h_run
    simp at h_run
  | some targetLoc =>
    rw [h_lookup] at h_run
    -- With empty loopContracts, there are no entries.
    have h_lc : (∅ : Std.HashMap String (Imperative.MetaData Core.Expression))[label]? = none := by
      simp
    rw [h_lc] at h_run
    simp [pure, Except.pure] at h_run
    rw [← h_run]

/-- The patch step preserves `size_eq` when `loopContracts` is empty. -/
theorem coreCFGToGotoPatchStep_preserves_size_eq_no_contracts
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (h_size : acc.2.instructions.size = acc.2.nextLoc) :
    acc'.2.instructions.size = acc'.2.nextLoc := by
  rw [coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc' idxLabel h_run]
  exact h_size

/-- The patch step preserves `locationNum_eq_index` when `loopContracts` is empty. -/
theorem coreCFGToGotoPatchStep_preserves_locationNum_no_contracts
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        acc.2.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      acc'.2.instructions[i]? = some instr → instr.locationNum = i := by
  rw [coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc' idxLabel h_run]
  exact h_loc

/-- The patches-fold preserves the transform under empty loop contracts. -/
theorem patchesFoldlM_no_contracts_trans_eq
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc') :
    acc'.2 = acc.2 := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp at h_run
      have h_eq₁ : acc₁.2 = acc.2 :=
        coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc₁ head h_step
      rw [ih acc₁ h_run, h_eq₁]
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The patches-fold preserves `size_eq` (no loop contracts). -/
theorem patchesFoldlM_preserves_size_eq_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_size : acc.2.instructions.size = acc.2.nextLoc) :
    acc'.2.instructions.size = acc'.2.nextLoc := by
  -- Convert to list-foldlM for inductive reasoning.
  rw [← Array.foldlM_toList] at h_run
  -- Now `patches.toList.foldlM ... acc = .ok acc'`.
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_size₁ : acc₁.2.instructions.size = acc₁.2.nextLoc :=
        coreCFGToGotoPatchStep_preserves_size_eq_no_contracts labelMap acc acc₁ head h_step h_size
      exact ih acc₁ h_size₁ h_run
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The patches-fold preserves `locationNum_eq_index` (no loop contracts). -/
theorem patchesFoldlM_preserves_locationNum_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        acc.2.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      acc'.2.instructions[i]? = some instr → instr.locationNum = i := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_loc₁ :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            acc₁.2.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoPatchStep_preserves_locationNum_no_contracts
          labelMap acc acc₁ head h_step h_loc
      exact ih acc₁ h_loc₁ h_run
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Structural soundness of the translator output

`coreCFGToGotoTransform_size_eq_and_loc` is the structural half of the
top-level theorem: under the right hypotheses, the translator's output
satisfies `instructions.size = nextLoc` and every instruction's
`locationNum` equals its array index. This is the foundation for the
remaining layout fields of the eventual `CoreCFGToGotoTransformShadow`. -/

/-- After the translator runs (under no-loop-contracts and admitted-cmds
hypotheses), the output `ans : GotoTransform` satisfies:
* `ans.instructions.size = ans.nextLoc`,
* every instruction's `locationNum` equals its array index. -/
theorem coreCFGToGotoTransform_size_eq_and_loc
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState)
      = Except.ok st_final)
    (h_loopContracts_empty : st_final.loopContracts = ∅)
    (resolved : List (Nat × Nat))
    (trans_post : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_patches_run :
      st_final.pendingPatches.foldlM
        (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
        ([], st_final.trans)
      = Except.ok (resolved, trans_post))
    (h_ans_eq : ans = Imperative.patchGotoTargets trans_post resolved) :
    ans.instructions.size = ans.nextLoc ∧
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  -- Step 1: the blocks-fold preserves size_eq + locationNum_eq_index.
  have h_size_st : st_final.trans.instructions.size = st_final.trans.nextLoc :=
    blocksFoldlM_preserves_size_eq functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb) h_blocks_run h_init_size
  have h_loc_st :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st_final.trans.instructions[i]? = some instr → instr.locationNum = i :=
    blocksFoldlM_preserves_locationNum_eq_index functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb) h_blocks_run h_init_size h_init_loc
  -- Step 2: the patches-fold preserves them under the empty-loopContracts hypothesis.
  rw [h_loopContracts_empty] at h_patches_run
  have h_size_post : trans_post.instructions.size = trans_post.nextLoc :=
    patchesFoldlM_preserves_size_eq_no_contracts st_final.labelMap _
      ([], st_final.trans) (resolved, trans_post) h_patches_run h_size_st
  have h_loc_post :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans_post.instructions[i]? = some instr → instr.locationNum = i :=
    patchesFoldlM_preserves_locationNum_no_contracts st_final.labelMap _
      ([], st_final.trans) (resolved, trans_post) h_patches_run h_loc_st
  -- Step 3: patchGotoTargets preserves them.
  have h_size_ans : ans.instructions.size = ans.nextLoc := by
    rw [h_ans_eq]
    rw [patchGotoTargets_preserves_size, patchGotoTargets_preserves_nextLoc]
    exact h_size_post
  have h_loc_ans :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        ans.instructions[i]? = some instr → instr.locationNum = i := by
    intro i instr h
    rw [h_ans_eq] at h
    exact patchGotoTargets_preserves_locationNum_eq_index trans_post resolved h_loc_post i instr h
  exact ⟨h_size_ans, h_loc_ans⟩

/-! ### Translator decomposition

Initial state for the translator's forward pass and an explicit
unfolding of the translator into `do let st ← ...; let (r, t) ← ...;
return ...` form. -/

/-- Initial loop-state for `coreCFGToGotoTransform`'s forward pass. -/
@[expose] def coreCFGToGotoInitState
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    : Strata.CoreCFGTransLoopState :=
  { trans := trans₀, pendingPatches := #[], labelMap := {}, loopContracts := {} }

/-- The translator's output factors through the post-blocks-fold,
post-patches-fold, and a final `patchGotoTargets`. The proof works by
case-analysis on `cfg.blocks` to dispense with the entry-check, then
walking the two foldlM chains with `match`. -/
theorem coreCFGToGotoTransform_decompose
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ∃ (st_final : Strata.CoreCFGTransLoopState)
      (resolved : List (Nat × Nat))
      (trans_post : Imperative.GotoTransform Core.Expression.TyEnv),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final ∧
      st_final.pendingPatches.foldlM
        (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
        ([], st_final.trans)
      = Except.ok (resolved, trans_post) ∧
      ans = Imperative.patchGotoTargets trans_post resolved := by
  unfold Strata.coreCFGToGotoTransform at h_run
  -- Two cases on cfg.blocks for the entry-check; both dispatch to the same body.
  -- We use a unified strategy: rewrite the entry-check to `pure ()` first when the
  -- entry condition holds; in the empty-blocks case, the entry-check is `pure ()`
  -- directly. Use `match` on cfg.blocks via h_blocks.
  match h_blocks : cfg.blocks with
  | [] =>
    -- With empty blocks, both folds are trivial and the entry-check is `pure ()`.
    -- After the `match h_blocks : cfg.blocks with | [] =>`, in this branch
    -- `cfg.blocks` may already be substituted, so we don't `rw [h_blocks]`.
    refine ⟨coreCFGToGotoInitState trans₀, [], trans₀, ?_, ?_, ?_⟩
    · -- Goal: [].foldlM ... = ok (initState trans₀). Holds by rfl.
      rfl
    · rfl
    · -- ans = patchGotoTargets trans₀ [].
      rw [h_blocks] at h_run
      simp only [Bind.bind, Except.bind, pure, Except.pure, List.foldlM] at h_run
      injection h_run with h_run
      rw [← h_run]
  | (firstLabel, firstBlk) :: tail =>
    rw [h_blocks] at h_run
    simp only at h_run
    by_cases h_eq : firstLabel = cfg.entry
    · -- Entry match; if-bypassed.
      have h_neq : (firstLabel != cfg.entry) = false := by simp [h_eq]
      simp only [h_neq, Bool.false_eq_true, if_false] at h_run
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
      -- Match on the blocks-fold result. Use the literal initSt record so it unifies with h_run.
      generalize h_blocks_fold :
        ((firstLabel, firstBlk) :: tail).foldlM
          (Strata.coreCFGToGotoBlockStep functionName)
          ({ trans := trans₀, pendingPatches := #[], labelMap := {},
             loopContracts := {} } : Strata.CoreCFGTransLoopState)
          = blocks_fold at h_run
      match blocks_fold, h_blocks_fold with
      | .ok st_final, h_blocks_fold =>
        simp only at h_run -- reduce `match Except.ok st_final` step
        generalize h_patches_fold :
          st_final.pendingPatches.foldlM
            (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
            ([], st_final.trans) = patches_fold at h_run
        match patches_fold, h_patches_fold with
        | .ok (resolved, trans_post), h_patches_fold =>
          refine ⟨st_final, resolved, trans_post, ?_, h_patches_fold, ?_⟩
          · -- Goal: ((firstLabel, firstBlk) :: tail).foldlM ... (initState trans₀) = ok st_final.
            -- (cfg.blocks already substituted by Lean's match-rewrite.)
            -- coreCFGToGotoInitState unfolds to the literal record in h_blocks_fold.
            simp only [coreCFGToGotoInitState]
            exact h_blocks_fold
          · simp only at h_run
            injection h_run with h_run; rw [← h_run]
        | .error _, _ => simp at h_run
      | .error _, _ => simp at h_run
    · -- Entry mismatch; throws.
      have h_neq : (firstLabel != cfg.entry) = true := by simp [h_eq]
      simp only [h_neq, if_true, throw, throwThe, MonadExcept.throw,
                 Bind.bind, Except.bind] at h_run
      cases h_run

/-! ### Direct structural soundness

Composes `coreCFGToGotoTransform_decompose` with
`coreCFGToGotoTransform_size_eq_and_loc` to deliver the structural
guarantees of `coreCFGToGotoTransform`'s output directly from input
hypotheses + a "post-blocks-fold loopContracts is empty" hypothesis. -/

/-- The translator's output satisfies `size_eq` and
`locationNum_eq_index`, given input hypotheses + the post-blocks-fold
hypothesis that `loopContracts` is empty (true for any CFG without
loop-invariant or decreases metadata). -/
theorem coreCFGToGotoTransform_size_eq_and_loc_direct
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ans.instructions.size = ans.nextLoc ∧
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  exact coreCFGToGotoTransform_size_eq_and_loc Env functionName cfg trans₀
    h_init_size h_init_loc h_admitted_blocks ans h_run
    st_final h_blocks_run (h_loopContracts_empty_post st_final h_blocks_run)
    resolved trans_post h_patches_run h_ans_eq



/-- The hypothesis bundle for `coreCFGToGotoTransform_wellFormed_via_shadow`:
captures all the facts that an outer-loop equivalence proof must
supply about the `coreCFGToGotoTransform`'s output. -/
structure CoreCFGToGotoTransformShadow
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression) where
  /-- The final labelMap, total over `cfg.blocks`. -/
  finalLabelMap : LabelMap
  /-- Every CFG block label has a `pc` in `finalLabelMap`. -/
  labelMap_total :
    ∀ l, l ∈ cfg.blocks.map Prod.fst → (finalLabelMap l).isSome
  /-- Distinct labels map to distinct `pc`s. -/
  labelMap_inj :
    ∀ l₁ l₂ pc, finalLabelMap l₁ = some pc → finalLabelMap l₂ = some pc → l₁ = l₂
  /-- The `instructions.size = nextLoc` invariant on the final state. -/
  size_eq : ans.instructions.size = ans.nextLoc
  /-- Every instruction's `locationNum = index`. -/
  locationNum_eq_index :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i
  /-- For each CFG block label, `instrAt` of its `pc` returns a LOCATION
  instruction. -/
  layout_location :
    ∀ l blk pc,
      (l, blk) ∈ cfg.blocks → finalLabelMap l = some pc →
      ∃ instr, ans.instructions[pc]? = some instr ∧ instr.type = .LOCATION
  /-- For each `condGoto` block, two GOTO instructions appear at the
  end with proper targets. -/
  layout_cond_goto :
    ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
        pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
        pc_uncond = pc_neg + 1 ∧
        ans.instructions[pc_neg]? = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = some pc_lf ∧
        finalLabelMap lf = some pc_lf ∧
        ans.instructions[pc_uncond]? = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = some pc_lt ∧
        finalLabelMap lt = some pc_lt
  /-- The condGoto guards have the right shape. -/
  layout_cond_goto_guards :
    ∀ l blk pc cond lt lf md instr_neg instr_uncond,
      (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond →
      ∃ e_goto,
        instr_neg.guard = e_goto.not ∧
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
        instr_uncond.guard = CProverGOTO.Expr.true
  /-- For each `finish` block, an END_FUNCTION appears after the body. -/
  layout_finish :
    ∀ l blk pc md, (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .finish md →
      ∃ pc_end instr_end,
        pc_end = pc + 1 + DetBlockBodyInstrCount blk ∧
        ans.instructions[pc_end]? = some instr_end ∧
        instr_end.type = .END_FUNCTION
  /-- For each block body, the per-Cmd layout holds. -/
  layout_block_body :
    ∀ l blk pc, (l, blk) ∈ cfg.blocks → finalLabelMap l = some pc →
    ∀ k inner,
      (h : k < blk.cmds.length) →
      blk.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions } -- temporary program
        (pc + 1 + cmdsPrefixInstrCount blk.cmds k)
        inner
  /-- The CFG's entry label is in the map. -/
  entry_in_map : ∃ pc, finalLabelMap cfg.entry = some pc

/-- Bridge from `CoreCFGToGotoTransformShadow` to
`WellFormedTranslation`: build the witness over the program whose
instructions equal `ans.instructions`. The bridge is essentially a
field-by-field copy — each field of `WellFormedTranslation` is provided
directly by the corresponding field of `CoreCFGToGotoTransformShadow`,
modulo the `instrAt`-vs-`instructions[?]` rephrasing.

This lemma's existence means the *only* remaining work to close the
top-level theorem is producing a `CoreCFGToGotoTransformShadow` from
the actual translator's output — i.e., the outer-loop equivalence
proof. Once that lands, this lemma converts it directly into a
`WellFormedTranslation`. -/
def wellFormedTranslation_of_shadow
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (shadow : CoreCFGToGotoTransformShadow cfg Env functionName
                trans₀ ans δ δ_goto δ_goto_bool) :
    WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool where
  labelMap := shadow.finalLabelMap
  labelMap_total := shadow.labelMap_total
  labelMap_inj := shadow.labelMap_inj
  layout_location := by
    intro l blk pc h_in h_lookup
    obtain ⟨instr, h_at, h_ty⟩ := shadow.layout_location l blk pc h_in h_lookup
    refine ⟨instr, ?_, h_ty⟩
    -- Goal: pgm.instrAt pc = some instr, where pgm.instructions = ans.instructions.
    show ans.instructions[pc]? = some instr
    exact h_at
  layout_cond_goto := by
    intro l blk pc cond lt lf md h_in h_lookup h_transfer
    obtain ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
            h_pc_neg, h_pc_uncond, h_at_neg, h_ty_neg, h_target_neg, h_lf_lookup,
            h_at_uncond, h_ty_uncond, h_target_uncond, h_lt_lookup⟩ :=
      shadow.layout_cond_goto l blk pc cond lt lf md h_in h_lookup h_transfer
    refine ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
            h_pc_neg, h_pc_uncond, ?_, h_ty_neg, h_target_neg, h_lf_lookup,
            ?_, h_ty_uncond, h_target_uncond, h_lt_lookup⟩
    · show ans.instructions[pc_neg]? = some instr_neg
      exact h_at_neg
    · show ans.instructions[pc_uncond]? = some instr_uncond
      exact h_at_uncond
  layout_cond_goto_guards := by
    intro l blk pc cond lt lf md instr_neg instr_uncond h_in h_lookup h_transfer h_neg h_uncond
    -- The hypotheses use Program.instrAt; convert to ans.instructions[?].
    have h_neg' : ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg := h_neg
    have h_uncond' : ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond := h_uncond
    exact shadow.layout_cond_goto_guards l blk pc cond lt lf md instr_neg instr_uncond
      h_in h_lookup h_transfer h_neg' h_uncond'
  layout_finish := by
    intro l blk pc md h_in h_lookup h_transfer
    obtain ⟨pc_end, instr_end, h_pc_end, h_at_end, h_ty_end⟩ :=
      shadow.layout_finish l blk pc md h_in h_lookup h_transfer
    refine ⟨pc_end, instr_end, h_pc_end, ?_, h_ty_end⟩
    show ans.instructions[pc_end]? = some instr_end
    exact h_at_end
  layout_block_body := shadow.layout_block_body
  entry_in_map := shadow.entry_in_map
  locationNum_eq_index := by
    intro i instr h
    -- Goal: instr.locationNum = i, where h : pgm.instrAt i = some instr.
    -- pgm.instrAt i = ans.instructions[i]? by the program's instructions field.
    have h' : ans.instructions[i]? = some instr := h
    exact shadow.locationNum_eq_index i instr h'

/-! ## Top-level theorem

`coreCFGToGotoTransform_wellFormed_nonempty` proves
`Nonempty (WellFormedTranslation ...)` — there exists a witness for
the well-formedness predicate over the translator's output. The proof
composes:

1. `coreCFGToGotoTransform_size_eq_and_loc_direct` (size_eq + locationNum).
2. `blocksFoldlM_layout_location` and `blocksFoldlM_layout_finish` for
   the LOCATION and END_FUNCTION layouts.
3. `patchGotoTargets_preserves_type` to bridge from
   `st_final.trans.instructions` to `ans.instructions`.
4. External hypotheses for the unproven layout fields
   (`layout_cond_goto`, `layout_cond_goto_guards`, `layout_block_body`,
   `labelMap_inj`, `entry_in_map`).

`Nonempty` form sidesteps the motive-typing issues with
`Classical.choose` on `coreCFGToGotoTransform_decompose`'s ∃-witness:
the goal is now a `Prop` (`Nonempty _`) so `obtain` on the `∃` works
directly. -/

/-- Top-level theorem in `Nonempty` form: `coreCFGToGotoTransform`
produces a `WellFormedTranslation`-witnessed program (under the
hypotheses). -/
theorem coreCFGToGotoTransform_wellFormed_nonempty
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_layout_cond_goto :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
        blk.transfer = .condGoto cond lt lf md →
        ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
          pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
          pc_uncond = pc_neg + 1 ∧
          ans.instructions[pc_neg]? = some instr_neg ∧
          instr_neg.type = .GOTO ∧
          instr_neg.target = some pc_lf ∧
          hashMapToLabelMap st_final.labelMap lf = some pc_lf ∧
          ans.instructions[pc_uncond]? = some instr_uncond ∧
          instr_uncond.type = .GOTO ∧
          instr_uncond.target = some pc_lt ∧
          hashMapToLabelMap st_final.labelMap lt = some pc_lt)
    (h_layout_cond_goto_guards :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc cond lt lf md instr_neg instr_uncond,
        (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
        blk.transfer = .condGoto cond lt lf md →
        ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg →
        ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond →
        ∃ e_goto,
          instr_neg.guard = e_goto.not ∧
          ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
          instr_uncond.guard = CProverGOTO.Expr.true)
    (h_layout_block_body :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc, (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
      ∀ k inner,
        (h : k < blk.cmds.length) →
        blk.cmds[k]'h = .cmd inner →
        CmdEmittedAt δ δ_goto δ_goto_bool
          { name := "", parameterIdentifiers := #[],
            instructions := ans.instructions }
          (pc + 1 + cmdsPrefixInstrCount blk.cmds k)
          inner)
    (h_labelMap_inj :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l₁ l₂ pc,
        hashMapToLabelMap st_final.labelMap l₁ = some pc →
        hashMapToLabelMap st_final.labelMap l₂ = some pc →
        l₁ = l₂)
    (h_entry_in_map :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∃ pc, hashMapToLabelMap st_final.labelMap cfg.entry = some pc) :
    Nonempty (WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool) := by
  -- Decompose the translator's output (in Prop, so obtain works).
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- size_eq + locationNum_eq_index from structural soundness.
  obtain ⟨h_size_ans, h_loc_ans⟩ :=
    coreCFGToGotoTransform_size_eq_and_loc_direct Env functionName cfg trans₀
      h_init_size h_init_loc
      (fun l blk h_in c h_c => h_admitted_blocks l blk h_in c h_c)
      h_loopContracts_empty_post ans h_run
  -- Layout lemmas at the post-blocks-fold state.
  have h_layout_loc_st :=
    blocksFoldlM_layout_location functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run h_init_size h_distinct
  have h_layout_fin_st :=
    blocksFoldlM_layout_finish functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run h_init_size h_distinct
  -- Patches + patchGotoTargets preserve the array under loop-contracts-empty.
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  -- Helper: at any pc, ans.instructions[pc]? gives some instr with type
  -- preserved from st_final.trans.instructions[pc]?.
  have h_ans_eq' : ans = Imperative.patchGotoTargets st_final.trans resolved := by
    rw [h_ans_eq, h_trans_post_eq]
  have h_ans_type_at :
      ∀ (pc : Nat) (instr_st : CProverGOTO.Instruction),
        st_final.trans.instructions[pc]? = some instr_st →
        ∃ instr_ans,
          ans.instructions[pc]? = some instr_ans ∧
          instr_ans.type = instr_st.type := by
    intro pc instr_st h_at_st
    have h_size_ans' : ans.instructions.size = st_final.trans.instructions.size := by
      rw [h_ans_eq']
      exact patchGotoTargets_preserves_size st_final.trans resolved
    have h_pc_lt : pc < ans.instructions.size := by
      have h_st_lt : pc < st_final.trans.instructions.size :=
        Array.getElem?_eq_some_iff.mp h_at_st |>.1
      omega
    have h_at_ans_eq : ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
      rw [h_ans_eq']
    have h_at_ans : ans.instructions[pc]? = some ans.instructions[pc] :=
      Array.getElem?_eq_getElem h_pc_lt
    refine ⟨ans.instructions[pc], h_at_ans, ?_⟩
    -- Use patchGotoTargets_preserves_type. The hypothesis h_at_ans is over
    -- ans.instructions; we rewrite to get over patchGotoTargets.
    have h_at_patched :
        (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc]? = some ans.instructions[pc] := by
      rw [← h_at_ans_eq]; exact h_at_ans
    obtain ⟨instr_pre, h_at_pre, h_ty_eq⟩ :=
      patchGotoTargets_preserves_type st_final.trans resolved pc _ h_at_patched
    rw [h_at_pre] at h_at_st
    injection h_at_st with h_at_st
    rw [h_ty_eq]; rw [← h_at_st]
  -- labelMap_total: every block label is in st_final.labelMap.
  have h_labelMap_total :
      ∀ l, l ∈ cfg.blocks.map Prod.fst →
        (hashMapToLabelMap st_final.labelMap l).isSome := by
    intro l h_in
    rw [List.mem_map] at h_in
    obtain ⟨p, h_in', h_eq⟩ := h_in
    obtain ⟨l', blk⟩ := p
    simp at h_eq
    subst h_eq
    obtain ⟨pc, _, h_lookup, _, _, _⟩ := h_layout_loc_st l' blk h_in'
    show (st_final.labelMap[l']?).isSome
    rw [h_lookup]; rfl
  -- Build the shadow.
  refine ⟨wellFormedTranslation_of_shadow cfg Env functionName trans₀ ans
            δ δ_goto δ_goto_bool ?_⟩
  exact {
    finalLabelMap := hashMapToLabelMap st_final.labelMap
    labelMap_total := h_labelMap_total
    labelMap_inj := h_labelMap_inj st_final h_blocks_run
    size_eq := h_size_ans
    locationNum_eq_index := h_loc_ans
    layout_location := by
      intro l blk pc h_in h_lookup
      obtain ⟨pc', instr, h_lookup', h_at_st, h_ty_st, _⟩ := h_layout_loc_st l blk h_in
      have h_pc_eq : pc = pc' := by
        unfold hashMapToLabelMap at h_lookup
        rw [h_lookup'] at h_lookup
        exact (Option.some.inj h_lookup).symm
      obtain ⟨instr_ans, h_at_ans, h_ty_eq⟩ := h_ans_type_at pc' instr h_at_st
      refine ⟨instr_ans, h_pc_eq ▸ h_at_ans, ?_⟩
      rw [h_ty_eq]; exact h_ty_st
    layout_cond_goto := h_layout_cond_goto st_final h_blocks_run
    layout_cond_goto_guards := h_layout_cond_goto_guards st_final h_blocks_run
    layout_finish := by
      intro l blk pc md h_in h_lookup h_transfer
      obtain ⟨pc', instr_end, h_lookup', h_at_st, h_ty_st⟩ :=
        h_layout_fin_st l blk md h_in h_transfer
      have h_pc_eq : pc = pc' := by
        unfold hashMapToLabelMap at h_lookup
        rw [h_lookup'] at h_lookup
        exact (Option.some.inj h_lookup).symm
      obtain ⟨instr_ans, h_at_ans, h_ty_eq⟩ := h_ans_type_at _ instr_end h_at_st
      refine ⟨pc' + 1 + DetBlockBodyInstrCount blk, instr_ans, h_pc_eq ▸ rfl, h_pc_eq ▸ h_at_ans, ?_⟩
      rw [h_ty_eq]; exact h_ty_st
    layout_block_body := h_layout_block_body st_final h_blocks_run
    entry_in_map := h_entry_in_map st_final h_blocks_run
  }

/-! Documentation of the original (round 2) plan for the
`coreCFGToGotoTransform_wellFormed` theorem. Round 4 has now closed
this in `Nonempty` form (see `coreCFGToGotoTransform_wellFormed_nonempty`
above) — the structural soundness theorem and the lifted layout
lemmas (`blocksFoldlM_layout_location`, `blocksFoldlM_layout_finish`)
discharge the proven shadow fields, and hypotheses cover
`layout_cond_goto`, `layout_cond_goto_guards`, `layout_block_body`,
`labelMap_inj`, and `entry_in_map`.

Original round 2 sketch (kept for reference, includes an `admit`
inside a markdown block — not a live proof):

```lean
theorem coreCFGToGotoTransform_wellFormed
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc : ∀ i instr, trans₀.instructions[i]? = some instr →
                              instr.locationNum = i)
    (h_distinct : List.Pairwise (· ≠ ·) (cfg.blocks.map Prod.fst))
    (h_admitted_blocks :
      ∀ l blk, (l, blk) ∈ cfg.blocks →
      ∀ k h, Core.CmdExt.isAdmittedCmd (blk.cmds[k]'h) = true)
    (h_blocks_nonempty : ∀ l blk, (l, blk) ∈ cfg.blocks → True)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq : ∀ e, Imperative.ToGoto.toGotoExpr e = .ok (h_expr_corr.tx e)) :
    WellFormedTranslation cfg
      { name := functionName, parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool := by
  -- Build the shadow witness from the actual translator's output.
  have shadow : CoreCFGToGotoTransformShadow cfg Env functionName
                  trans₀ ans δ δ_goto δ_goto_bool := by
    -- HERE: the missing 500-900 LoC outer-loop equivalence proof.
    -- It walks `coreCFGToGotoTransform`'s body, threading the partial
    -- WF invariant through emitLabel + innerCmdLoop + transfer-emit +
    -- patchGotoTargets, building each shadow field.
    admit -- placeholder; replace with the loop-induction proof.
  exact wellFormedTranslation_of_shadow cfg Env functionName
    trans₀ ans δ δ_goto δ_goto_bool shadow
```

The body's `admit` is the loop-induction work — *this code is in a
documentation block, not in the live module*. Everything else
(per-emit preservation, per-Cmd dispatcher, `innerCmdLoop_layout_block_body`,
`labelMapInsert` invariants, `wellFormedTranslation_of_shadow`) is
already proven in this file. -/

end -- public section

end CProverGOTO
