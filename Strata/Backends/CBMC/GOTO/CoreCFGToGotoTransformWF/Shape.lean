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

/-! # WellFormedTranslation - Per-Cmd shape lemmas

This file is part 1 of the CoreCFGToGotoTransformWF split. It provides
the foundational shape lemmas for Cmd.toGotoInstructions, the emit helpers,
and patchGotoTargets, plus the per-Cmd CmdEmittedAt builders and the
per-shape dispatcher.
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

Bridges from the per-`Cmd` shape lemmas above to the `CmdEmittedAt`
predicate consumed by `WellFormedTranslation`. Each takes:

* the result `ans` of `Cmd.toGotoInstructions` (matched via the
  corresponding shape lemma),
* an `ExprTranslated` witness for the relevant translated expression,
* a final program `pgm` whose `instructions` contains `ans.instructions`
  as a prefix (i.e., `pgm.instructions[k]? = ans.instructions[k]?` for
  every `k < ans.instructions.size`),

and produces `CmdEmittedAt pgm trans.nextLoc cmd`. The "prefix" form
abstracts away the patching pass and the trailing instructions emitted
by later blocks. One bridge per `Imperative.Cmd` constructor.
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
    (e_goto : Expr) (gty : CProverGOTO.Ty)
    (h_decl_code : i_decl.code = Code.decl
      (Expr.symbol (Imperative.ToGoto.identToString (P := Core.Expression) v) gty))
    (h_assn_code : i_assn.code = Code.assign
      (Expr.symbol (Imperative.ToGoto.identToString (P := Core.Expression) v) gty)
      e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.init v ty (.det e_core) md) :=
  CmdEmittedAt.init_det pc v ty e_core md i_decl i_assn
    h_decl_at h_decl_ty h_assn_at h_assn_ty e_goto gty
    h_decl_code h_assn_code h_translated

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
    (h_decl_ty : i_decl.type = .DECL)
    (gty : CProverGOTO.Ty)
    (h_decl_code : i_decl.code = Code.decl
      (Expr.symbol (Imperative.ToGoto.identToString (P := Core.Expression) v) gty)) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.init v ty .nondet md) :=
  CmdEmittedAt.init_nondet pc v ty md i_decl h_decl_at h_decl_ty
    gty h_decl_code

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
    (e_goto : Expr) (gty : CProverGOTO.Ty)
    (h_assn_code : i_assn.code = Code.assign
      (Expr.symbol (Imperative.ToGoto.identToString (P := Core.Expression) v) gty)
      e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v (.det e_core) md) :=
  CmdEmittedAt.set_det pc v e_core md i_assn
    h_assn_at h_assn_ty e_goto gty h_assn_code h_translated

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

/-! ## Per-`Cmd` driver lemmas

The per-Cmd drivers package each `Cmd.toGotoInstructions` case into a
`CmdEmittedAt` builder, taking the loop invariant
`trans.instructions.size = trans.nextLoc` explicitly. -/

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
    v e md i_assn h_at h_assn_ty e_goto gty h_assn_code h_translated

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
  obtain ⟨gty, i_decl, _h_ty, h_decl_ty, h_decl_code, _h_decl_loc,
    h_inst, _h_next, _h_T⟩ :=
    Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
  have h_at : pgm.instrAt trans.nextLoc = some i_decl :=
    pgm_instrAt_of_push_invariant pgm trans.instructions i_decl ans.instructions
      trans.nextLoc h_invariant h_inst h_prefix
  exact cmdEmittedAt_init_nondet δ δ_goto δ_goto_bool pgm trans.nextLoc
    v ty md i_decl h_at h_decl_ty gty h_decl_code

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
          h_decl_ty, h_decl_code, _h_decl_loc,
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
    e_goto gty h_decl_code h_assn_code h_translated

/-! ## `set_nondet` shape and driver

Structurally similar to the four other single-instruction emit cases
(single ASSIGN at `pc`), but with a side-effect-Nondet RHS rather than
a translated expression. -/

/-- `.set v .nondet md` succeeds iff `lookupType T v` succeeds; the
result has one new ASSIGN appended whose RHS is a side-effect Nondet.
The lhs is exposed as `Expr.symbol (identToString v) gty` and the rhs's
`id`/`type` are exposed (matching `CmdEmittedAt.set_nondet`). -/
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
      (∃ e_nondet,
        i_assn.code = Code.assign
          (Expr.symbol (Imperative.ToGoto.identToString (P := Core.Expression) v) gty)
          e_nondet ∧
        e_nondet.id = .side_effect .Nondet ∧
        e_nondet.type = gty) ∧
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
      rfl, rfl,
      ⟨{ id := .side_effect .Nondet, sourceLoc := srcLoc, type := gty },
        rfl, rfl, rfl⟩,
      rfl, ?_, ?_⟩
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
    (gty : CProverGOTO.Ty)
    (h_assn_code : ∃ e_nondet,
      i_assn.code = Code.assign
        (Expr.symbol (Imperative.ToGoto.identToString (P := Core.Expression) v) gty)
        e_nondet ∧
      e_nondet.id = .side_effect .Nondet ∧
      e_nondet.type = gty) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v .nondet md) :=
  CmdEmittedAt.set_nondet pc v md i_assn h_assn_at h_assn_ty gty h_assn_code

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
  obtain ⟨gty, i_assn, _h_ty, h_assn_ty, h_assn_code, _h_loc, h_inst, _h_next⟩ :=
    Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
  have h_at : pgm.instrAt trans.nextLoc = some i_assn :=
    pgm_instrAt_of_push_invariant pgm trans.instructions i_assn ans.instructions
      trans.nextLoc h_invariant h_inst h_prefix
  exact cmdEmittedAt_set_nondet δ δ_goto δ_goto_bool pgm trans.nextLoc
    v md i_assn h_at h_assn_ty gty h_assn_code

/-! ## Per-Cmd dispatcher

Case-splits on an `Imperative.Cmd Core.Expression` admitted by
`isAdmittedCmd` and produces a `CmdEmittedAt` witness from a successful
`Cmd.toGotoInstructions` call, dispatching to the per-shape drivers
above. `.cover` and `.init _ _ .nondet` are excluded by
`isAdmittedCmd` and discharged contradictorily; `.set _ .nondet` is
admitted and routed through `cmdEmittedAt_set_nondet_of_toGotoInstructions`.
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


end -- public section

end CProverGOTO
