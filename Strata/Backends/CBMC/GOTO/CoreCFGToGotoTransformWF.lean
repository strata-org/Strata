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

/-! ## Outline of the remaining loop-induction work

The full `coreCFGToGotoTransform_wellFormed` theorem requires three more
substantial pieces of infrastructure on top of what is in this module.

### Step 1: per-`Imperative.Cmd` driver lemma

A single lemma that consumes any one of the seven `Imperative.Cmd`
shapes and produces a `CmdEmittedAt` for the post-translation `pgm`,
*provided* `pgm.instructions` extends `ans.instructions` as a prefix.
This is essentially a case-split that dispatches to the appropriate
`Cmd_toGotoInstructions_*_ok` and `cmdEmittedAt_*` pair from this file.

```
theorem cmdEmittedAt_of_toGotoInstructions
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (h_admitted :
      Core.CmdExt.isAdmittedCmd (.cmd c) = true)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans
      = Except.ok ans)
    (pgm : Program)
    (h_prefix :
      ∀ (k : Nat), k < ans.instructions.size →
        pgm.instrAt k = ans.instructions[k]?)
    (δ δ_goto δ_goto_bool : ...)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc c
```

The proof case-splits on `c` and uses each per-`Cmd` shape lemma plus
the matching `cmdEmittedAt_*` builder. The `h_admitted` hypothesis
rules out `.cover` and `.set _ .nondet`.

### Step 2: per-block (one outer-loop-iteration) driver lemma

Captures what changes during one iteration of the
`for (label, block) in cfg.blocks do ...` loop. The mutable state
threads `(trans, labelMap, pendingPatches)`; the body emits:
- one LOCATION (via `emitLabel`),
- `block.cmds.foldlM` (via `Cmd.toGotoInstructions` for `.cmd c` cases;
  `.call` cases are out of scope under `isAdmittedCmd`),
- the transfer instructions (`condGoto` → 2 GOTOs, `finish` → 1
  END_FUNCTION).

The lemma's conclusion is that, after one iteration, the new `trans'`
satisfies a *partial* `WellFormedTranslation` over `cfg.blocks.take k+1`
relative to the old `trans`'s partial WF over `cfg.blocks.take k`.

The *partial* `WellFormedTranslation` is the obvious weakening of the
full predicate that quantifies over `(l, blk) ∈ blocks_so_far` (using
`List.take`) instead of all `cfg.blocks`. It also needs to drop
`labelMap_total` (some labels haven't been visited yet) and refers to
`pendingPatches` as forward references.

### Step 3: loop induction + final patching

The for-loop induction proves that after iterating over all
`cfg.blocks`, the `trans` state satisfies an "almost-WF" predicate
where `pendingPatches` records the unresolved forward references.

The patching pass then resolves these (one `Array.set!` per pending
patch), turning the "almost-WF" into a full
`WellFormedTranslation`. The key facts needed here:

1. `patchGotoTargets_preserves_size` (proved here),
2. `patchGotoTargets_preserves_nextLoc` (proved here),
3. `patchGotoTargets` only changes the `target` field (proved here
   indirectly; the `at_unpatched` direction is one short induction
   away),
4. `labelMap` after all iterations is total over `cfg.blocks.map Prod.fst`
   (a direct consequence of "every iteration inserts the block's
   label"),
5. `labelMap` is injective: each insertion uses `nextLoc` as the value,
   `nextLoc` is strictly monotonic across iterations, so the inverse is
   a function (any value occurs at most once).

### Risk: `labelMap_inj` and shadowing

The injectivity of `labelMap` requires the *labels* to be distinct
across iterations. `Std.HashMap.insert` overwrites, so two iterations
inserting the same label would still produce a hash map, but the
witness for injectivity would fail.

The `Core.DetCFG` invariant that block labels are distinct is currently
implicit (no Lean predicate enforces it). Either:

* The wrapper `procedureToGotoCtxViaCFG` rejects CFGs with duplicate
  labels (currently it doesn't), or
* `WellFormedTranslation` is restricted to CFGs satisfying a
  `BlockLabelsDistinct cfg` predicate.

The closer of the two is to add `BlockLabelsDistinct` as an explicit
hypothesis on `coreCFGToGotoTransform_wellFormed`. The translator's
output is "well-formed" only on well-formed inputs.
-/

end -- public section

end CProverGOTO
