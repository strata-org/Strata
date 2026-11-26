/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.WPRewritePipelineProofs
import Strata.Util.OrderedSetProps
import Strata.Transform.WP.WPCoreProgramProps

/-! # The premises of the `--vcgen wp` pipeline theorems hold for an obligation unit

The lemma `lemma [l]: forall x : int :: x == x` becomes an obligation unit whose body asserts the
lemma's obligation over the fresh free variable `x@1 : int` (`WP.lemmaUnit`). That variable is
neither a parameter nor an alias of the unit. The free-variable clause of the entry gates
(`ObligationExtraction.WPPipelineEntryGates`) and the unit branch of the typing premise of the WP
phase's input (`ObligationExtraction.WPPhaseInputWellTyped`) hold for the unit; the unit's free
variable is not a parameter or an alias, and its body is not well typed under the unit's
(empty) parameter types. -/

namespace WPEntryGatesLemmaTest

open Core Imperative

/-- The free variable `x@1 : int` of the obligation. -/
def xv : Expression.Expr := .fvar Core.valueLoc ⟨"x@1", ()⟩ (some .int)

/-- The obligation of the lemma, `x@1 == x@1`. -/
def obl : Expression.Expr := .eq Core.valueLoc xv xv

/-- The body of the obligation unit: the assertion of the obligation. -/
def body : Statements := [.cmd (.cmd (.assert "l" obl #[]))]

/-- The obligation unit of the lemma, as `Decl.obligationProc` builds it. -/
def unit : Procedure :=
  { header := { name := ⟨"l", ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured body false }

/-- `x@1` is a free variable of the body. -/
theorem mem_freeVars_body : (⟨"x@1", ()⟩ : Expression.Ident) ∈ Block.freeVars body := by
  simp only [body, Block.freeVars, Stmt.freeVars, List.append_nil]
  exact (mem_exprFV (P := Expression)).2 (by simp [obl, xv, HasFvars.getFvars,
    Lambda.LExpr.LExpr.getVars])

/-- `unit` is an obligation unit. -/
example : WP.isObligationUnit unit = true := by simp [WP.isObligationUnit, unit, body]

/-- The free-variable clause of the entry gates holds for the unit: its free variable is neither
    assigned nor defined in its body. -/
example : ∀ x ∈ Block.freeVars body, x ∈ unit.entryParams ∨ x ∈ unit.oldAliases.map (·.1) ∨
    x ∉ Block.modifiedOrDefinedVars body false := fun _ _ => .inr (.inr (by
  simp [body, Block.modifiedOrDefinedVars, Block.modifiedVars, Stmt.modifiedVars,
    HasVarsImp.modifiedVars, CmdExt.modifiedVars, Cmd.modifiedVars, Block.definedVars,
    Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]))

/-- The free variable of the unit is neither a parameter nor an alias. -/
example : ¬ ∀ x ∈ Block.freeVars body, x ∈ unit.entryParams ∨ x ∈ unit.oldAliases.map (·.1) := by
  intro h
  have hk := h _ mem_freeVars_body
  simp only [unit, Procedure.entryParams, Strata.Util.OrderedSet.mem_eraseDups,
    Procedure.oldAliases, Procedure.Header.getInoutParams, getInoutParams, List.filter_nil,
    List.map_nil, List.not_mem_nil, or_false] at hk
  exact nomatch hk

/-- The body of the unit is well typed under the typing its annotations give
    (`Expression.annotationTyping`), as the unit branch of the typing premise of the WP phase's
    input asks. -/
example : ∃ Γ, Statements.WellTyped Γ (unit.contractWrapped body) := by
  refine ⟨Expression.annotationTyping obl, ?_⟩
  rw [Core.WP.contractWrapped_emptySpec unit body rfl rfl]
  refine ⟨⟨⟨trivial, trivial⟩, ⟨?_, trivial⟩, ⟨fun x ty h => ?_, trivial⟩⟩,
    ⟨fun _ => False, by simp [Stmt.nondetGround, CmdExt.nondetGround], trivial⟩⟩
  · refine ⟨.bool, rfl, Lambda.LConst.ty_isGround (.boolConst true), fun x τ h => ?_,
      .eq .fvar .fvar⟩
    simp only [obl, xv, Lambda.LExpr.freeVars, List.mem_append, List.mem_singleton, or_self,
      Prod.mk.injEq] at h
    exact ⟨.int, h.2, Lambda.LConst.ty_isGround (.intConst 0)⟩
  · simp only [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
      HasFvars.getTypedFvars, Expression.typedFvars, obl, xv, Lambda.LExpr.freeVars,
      List.cons_append, List.nil_append, Option.map_some, Option.some.injEq,
      List.filterMap_cons_some, List.filterMap_nil, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false, or_self] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Expression.annotationTyping, obl, xv, Lambda.LExpr.freeVars]

/-- The body of the unit is not well typed under the unit's (empty) parameter types. -/
example : ¬ Statements.WellTyped (fun x => WP.Tys.get? unit.paramTys x) body := by
  rintro ⟨⟨-, -, hW⟩, -⟩
  have h := hW.1 ⟨"x@1", ()⟩ (.forAll [] .int) (by
    simp [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars, obl, xv,
      HasFvars.getTypedFvars, Expression.typedFvars, Lambda.LExpr.freeVars])
  simp only [unit, Procedure.paramTys, Procedure.Header.getInoutParams, getInoutParams,
    WP.Tys.get?, List.filter_nil, List.map_nil, List.append_nil, Option.map_eq_some_iff] at h
  obtain ⟨_, hf, -⟩ := h
  exact nomatch hf

end WPEntryGatesLemmaTest
