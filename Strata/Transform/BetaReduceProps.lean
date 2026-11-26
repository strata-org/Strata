/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.BetaReduce
import all Strata.Transform.BetaReduce
import all Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExprWFProps
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.PipelinePhase

/-! # Properties of beta reduction

Beta reduction (`Lambda.LExpr.betaReduceRedexes`) substitutes arguments into bodies and erases
the arguments of constant lambdas, so it introduces no free variable and no operator: the free
variables and the operators of its result are among those of its input. Hence the phase keeps
the def-use well-formedness of every procedure body (`Block.defUseWellFormed`) for the same
defined-names and declared-functions predicates. The expression-level facts
(`Lambda.LExpr.getVars_betaReduceRedexesWith_subset`,
`Lambda.LExpr.getOps_betaReduceRedexesWith_subset`)
are in `Strata.DL.Lambda.LExprWFProps`.

- `Core.BetaReduce.betaReduceProgram_proc` — every procedure of the reduced program comes from a
  procedure of the input with the same header and metadata, whose structured body, def-use well
  formed, has a def-use well formed structured reduct
- `Core.betaReducePipelinePhase_ok` — a run of the phase is `betaReduceProgram`
-/

public section

namespace Core.BetaReduce

open Lambda Imperative

/-- A predicate holding of every element of a list holds of every element of a sublist. -/
private theorem all_of_subset {α : Type} {l l' : List α} {p : α → Bool} (hs : l' ⊆ l)
    (h : l.all p = true) : l'.all p = true :=
  List.all_eq_true.2 fun x hx => List.all_eq_true.1 h x (hs hx)

/-- Reducing the expressions of a command keeps the variables it defines and modifies, and
    keeps the variables it reads and the operators it uses among those of the command. -/
private theorem mapExpr_vars (c : Command) :
    HasVarsImp.readVars (P := Expression) (Command.mapExpr reduceExpr c) ⊆
        HasVarsImp.readVars (P := Expression) c ∧
      HasVarsImp.modifiedVars (P := Expression) (Command.mapExpr reduceExpr c) =
        HasVarsImp.modifiedVars (P := Expression) c ∧
      (∀ b, HasVarsImp.definedVars (P := Expression) (Command.mapExpr reduceExpr c) b =
        HasVarsImp.definedVars (P := Expression) c b) ∧
      HasOpsImp.getOps (P := Expression) (Command.mapExpr reduceExpr c) ⊆
        HasOpsImp.getOps (P := Expression) c := by
  have hv := LExpr.getVars_betaReduceRedexesWith_subset (T := CoreLParams.mono)
    LExpr.mergeMetadataForSubst
  have ho := LExpr.getOps_betaReduceRedexesWith_subset (T := CoreLParams.mono)
    LExpr.mergeMetadataForSubst
  rcases c with c | ⟨pname, tyArgs, args, md⟩
  · rcases c with ⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _ | _ | _ <;>
      simp [Command.mapExpr, HasVarsImp.readVars, HasVarsImp.modifiedVars, HasVarsImp.definedVars,
        HasOpsImp.getOps, CmdExt.readVars, CmdExt.modifiedVars, CmdExt.definedVars, CmdExt.getOps,
        Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars, Cmd.getOps, ExprOrNondet.getVars,
        HasFvars.getFvars, HasOps.getOps, reduceExpr, hv, ho]
  simp only [HasVarsImp.readVars, CmdExt.readVars, Command.mapExpr, HasFvars.getFvars,
    HasVarsImp.modifiedVars, CmdExt.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars,
    implies_true, HasOpsImp.getOps, CmdExt.getOps, HasOps.getOps, true_and]
  induction args with
  | nil => simp [Calls.getInputExprs, CallArg.getLhs]
  | cons a args ih =>
    cases a <;> simp only [Calls.getInputExprs, List.filterMap_map, CallArg.getLhs, List.map_cons,
      CallArg.mapInput, Option.some.injEq, List.filterMap_cons_some, List.flatMap_cons,
      List.filterMap_cons_none, List.cons.injEq, true_and] at ih ⊢
    · exact ⟨List.append_subset_append (hv _) ih.1, ih.2.1, List.append_subset_append (ho _) ih.2.2⟩
    · exact ⟨List.append_subset_append (List.Subset.refl _) ih.1, ih.2.1,
        List.append_subset_append (List.Subset.refl _) ih.2.2⟩
    · exact ih

/-- Reducing a statement keeps the variables it defines in the enclosing scope. -/
private theorem definedVars_reduceStmt (s : Statement) :
    Stmt.definedVars (reduceStmt s) true = Stmt.definedVars s true := by
  rcases s with c | _ | ⟨_ | _, _⟩ | ⟨_ | _, _⟩ | _ | _
  · simpa [reduceStmt] using (mapExpr_vars c).2.2.1 true
  all_goals simp [reduceStmt]

mutual
/-- Reducing a statement keeps its def-use well-formedness. -/
private theorem reduceStmt_defUse (D df : Expression.Ident → Bool) : ∀ (s : Statement),
    Stmt.defUseWellFormed D df s = true → Stmt.defUseWellFormed D df (reduceStmt s) = true
  | .cmd c, h => by
    obtain ⟨hr, hm, hd, ho⟩ := mapExpr_vars c
    simp only [reduceStmt, Stmt.defUseWellFormed, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨hr', hm'⟩, hd'⟩, ho'⟩ := h
    exact ⟨⟨⟨all_of_subset hr hr', hm ▸ hm'⟩, hd false ▸ hd'⟩, all_of_subset ho ho'⟩
  | .block l ss md, h => by
    simp only [reduceStmt, Stmt.defUseWellFormed] at h ⊢
    exact reduceBlock_defUse D df ss h
  | .ite (.det c) tss ess md, h => by
    simp only [reduceStmt, Stmt.defUseWellFormed, Bool.and_eq_true, ExprOrNondet.getVars,
      ExprOrNondet.getOps] at h ⊢
    obtain ⟨⟨⟨hv, ho⟩, ht⟩, he⟩ := h
    exact ⟨⟨⟨all_of_subset (LExpr.getVars_betaReduceRedexesWith_subset _ c) hv,
      all_of_subset (LExpr.getOps_betaReduceRedexesWith_subset _ c) ho⟩,
      reduceBlock_defUse D df tss ht⟩, reduceBlock_defUse D df ess he⟩
  | .ite .nondet tss ess md, h => by
    simp only [reduceStmt, Stmt.defUseWellFormed, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, reduceBlock_defUse D df tss h.1.2⟩, reduceBlock_defUse D df ess h.2⟩
  | .loop g m inv body md, h => by
    have hv := LExpr.getVars_betaReduceRedexesWith_subset (T := CoreLParams.mono)
      LExpr.mergeMetadataForSubst
    have ho := LExpr.getOps_betaReduceRedexesWith_subset (T := CoreLParams.mono)
      LExpr.mergeMetadataForSubst
    have hb := reduceBlock_defUse D df body
    rcases g with g | _ <;> rcases m with _ | m <;>
      simp only [Stmt.defUseWellFormed, ExprOrNondet.getVars, HasFvars.getFvars,
        ExprOrNondet.getOps, HasOps.getOps, Option.map_none, Option.getD_none, Option.map_some,
        Option.getD_some, List.all_nil, Bool.and_true, Bool.true_and, Bool.and_self,
        List.all_flatMap, Bool.and_eq_true, List.all_eq_true, Prod.forall, reduceStmt, List.all_map,
        Function.comp_apply, reduceExpr] at h hb ⊢ <;> grind
  | .exit .., _ | .typeDecl .., _ => by simp [reduceStmt, Stmt.defUseWellFormed]

/-- Reducing a statement list keeps its def-use well-formedness. -/
private theorem reduceBlock_defUse (D df : Expression.Ident → Bool) : ∀ (ss : Statements),
    Block.defUseWellFormed D df ss = true → Block.defUseWellFormed D df (reduceBlock ss) = true
  | [], h => by simp [reduceBlock, Block.defUseWellFormed]
  | s :: ss, h => by
    simp only [reduceBlock, Block.defUseWellFormed, Bool.and_eq_true] at h ⊢
    rw [definedVars_reduceStmt]
    exact ⟨reduceStmt_defUse D df s h.1, reduceBlock_defUse _ df ss h.2⟩
end

/-- **Beta reduction keeps the def-use well-formedness of procedure bodies.** Every procedure
    `q'` of `betaReduceProgram p` comes from a procedure `q` of `p` with the same header and
    metadata; when `q'` has a structured body, so has `q`, and the body of `q'` is def-use well
    formed for every defined-names and declared-functions predicates the body of `q` is. -/
theorem betaReduceProgram_proc {p : Program} {q' : Procedure} {md : MetaData Expression}
    (h : Decl.proc q' md ∈ (betaReduceProgram p).decls) :
    ∃ q, Decl.proc q md ∈ p.decls ∧ q'.header = q.header ∧
      ∀ ss' o, q'.body = .structured ss' o → ∃ ss, q.body = .structured ss o ∧
        ∀ D df, Block.defUseWellFormed D df ss = true →
          Block.defUseWellFormed D df ss' = true := by
  obtain ⟨_ | _ | _ | _ | _ | _ | _, hd, ⟨⟩⟩ := List.mem_map.1 h
  refine ⟨_, hd, rfl, fun ss' _ hb => ?_⟩
  split at hb <;> cases hb
  exact ⟨_, ‹_›, fun D df => reduceBlock_defUse D df _⟩

end Core.BetaReduce

/-- A run of `betaReducePipelinePhase` on `program` returns `betaReduceProgram program` and
    leaves the transform state as it is. -/
theorem Core.betaReducePipelinePhase_ok (program : Program) (s : Transform.CoreTransformState) :
    (betaReducePipelinePhase.transform program).run s =
      (.ok (true, BetaReduce.betaReduceProgram program), s) :=
  (rfl)

end -- public section
