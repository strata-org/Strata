/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.BetaReduceProps
public import Strata.Transform.Passive.CoreTyped
import all Strata.Transform.BetaReduce
import all Strata.Transform.BetaReduceProps
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.LExprTypedBeta

/-! # Beta reduction keeps right-hand sides typed

Beta reduction introduces no annotated free-variable occurrence
(`Lambda.LExpr.freeVars_betaReduceRedexes_subset`) and keeps the annotated typing
(`Lambda.LExpr.HasTypeA_betaReduceRedexes`), so it keeps a Core expression typed
(`Core.Expression.Typed_betaReduceRedexes`). Hence the phase keeps the annotation check
`Block.fvarTypesWellAnnotated` and the typed `init`s `Block.initsTyped` of every procedure body
(`Core.BetaReduce.betaReduceProgram_proc_typed`).

The free-variable lemmas of `Lambda.LExpr.betaReduceRedexes` are stated here rather than in
`Strata.DL.Lambda.LExprWFProps`, next to the typing facts they serve: only the typing proofs of
beta reduction use them.

Key theorems: `Core.Expression.Typed_betaReduceRedexes`,
`Core.BetaReduce.betaReduceProgram_proc_typed`. -/

public section

namespace Lambda.LExpr

/-- `freeVars` collects leaves. -/
private theorem collectsLeaves_freeVars {T : LExprParams} {G : Type} :
    CollectsLeaves (T := ⟨T, G⟩) LExpr.freeVars :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ e => by cases e <;> rfl⟩

/-- **Beta reduction introduces no annotated free-variable occurrence.** Every free-variable
    occurrence of `betaReduceRedexes e`, with its annotation, is one of `e`. -/
theorem freeVars_betaReduceRedexes_subset {T : LExprParams} (e : LExpr T.mono) :
    LExpr.freeVars (betaReduceRedexes e) ⊆ LExpr.freeVars e :=
  collectsLeaves_freeVars.betaReduceRedexesFuel _ _ _ e

/-- **Beta reduction under a metadata combinator introduces no annotated free-variable
    occurrence.** -/
theorem freeVars_betaReduceRedexesWith_subset {T : LExprParams}
    (merge : T.mono.base.Metadata → T.mono.base.Metadata → T.mono.base.Metadata →
      T.mono.base.Metadata) (e : LExpr T.mono) :
    LExpr.freeVars (betaReduceRedexesWith merge e) ⊆ LExpr.freeVars e :=
  collectsLeaves_freeVars.betaReduceRedexesFuel _ _ _ e

end Lambda.LExpr

namespace Core

open Lambda Imperative

/-- **Beta reduction keeps a Core expression typed.** -/
theorem Expression.Typed_betaReduceRedexes {e : Expression.Expr} {ty : Expression.Ty}
    (h : Expression.Typed e ty) : Expression.Typed (LExpr.betaReduceRedexes e) ty := by
  obtain ⟨τ, hτ, hg, ha, hT⟩ := h
  exact ⟨τ, hτ, hg, fun x τ? hx => ha x τ? (LExpr.freeVars_betaReduceRedexes_subset e hx),
    LExpr.HasTypeA_betaReduceRedexes hT⟩

/-- **Beta reduction under a metadata combinator keeps a Core expression typed**, as the
    pipeline's phase reduces (`LExpr.mergeMetadataForSubst`). -/
theorem Expression.Typed_betaReduceRedexesWith
    (merge : ExpressionMetadata → ExpressionMetadata → ExpressionMetadata → ExpressionMetadata)
    {e : Expression.Expr} {ty : Expression.Ty}
    (h : Expression.Typed e ty) : Expression.Typed (LExpr.betaReduceRedexesWith merge e) ty := by
  obtain ⟨τ, hτ, hg, ha, hT⟩ := h
  exact ⟨τ, hτ, hg, fun x τ? hx => ha x τ? (LExpr.freeVars_betaReduceRedexesWith_subset merge e hx),
    LExpr.HasTypeA_betaReduceRedexesWith merge hT⟩

namespace BetaReduce

/-- The annotated free-variable occurrences of a reduced expression are among those of the
    expression. -/
private theorem typedFvars_reduce (e : Expression.Expr) :
    HasFvars.getTypedFvars (P := Expression) (reduceExpr e) ⊆
      HasFvars.getTypedFvars (P := Expression) e := fun p hp => by
  obtain ⟨q, hq, hp⟩ := List.mem_filterMap.1 hp
  exact List.mem_filterMap.2 ⟨q, LExpr.freeVars_betaReduceRedexesWith_subset _ e hq, hp⟩

/-- Reducing the expressions of a command keeps its annotated reads among those of the command,
    its typed definitions, and its typed `init`. -/
private theorem mapExpr_typed (c : Command) :
    HasTypedVarsImp.typedReadVars (P := Expression) (Command.mapExpr reduceExpr c) ⊆
        HasTypedVarsImp.typedReadVars (P := Expression) c ∧
      HasTypedVarsImp.typedDefinedVars (P := Expression)
          (Command.mapExpr reduceExpr c) =
        HasTypedVarsImp.typedDefinedVars (P := Expression) c ∧
      (CmdExt.initsTyped Expression.Typed c →
        CmdExt.initsTyped Expression.Typed (Command.mapExpr reduceExpr c)) := by
  rcases c with c | ⟨pname, tyArgs, args, md⟩
  · rcases c with ⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _ | _ | _ <;>
      simp only [Command.mapExpr, HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars, ExprOrNondet.getTypedVars, HasTypedVarsImp.typedDefinedVars,
        CmdExt.typedDefinedVars, Cmd.typedDefinedVars, CmdExt.initsTyped, List.Subset.refl,
        true_and, and_true, imp_self] <;>
      first
      | exact ⟨typedFvars_reduce _, Expression.Typed_betaReduceRedexesWith _⟩
      | exact typedFvars_reduce _
  refine ⟨?_, rfl, fun _ => trivial⟩
  simp only [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Command.mapExpr]
  induction args with
  | nil => simp [Calls.getInputExprs]
  | cons a args ih =>
    cases a <;> simp only [Calls.getInputExprs, List.filterMap_cons, CallArg.mapInput,
      List.map_cons, List.flatMap_cons] at ih ⊢
    · exact List.append_subset_append (typedFvars_reduce _) ih
    · exact List.append_subset_append (List.Subset.refl _) ih
    · exact ih

/-- Reducing a statement keeps its typed definitions in the enclosing scope. -/
private theorem typedDefinedVars_reduceStmt (s : Statement) :
    Stmt.typedDefinedVars (reduceStmt s) = Stmt.typedDefinedVars s := by
  rcases s with c | _ | ⟨_ | _, _⟩ | ⟨_ | _, _⟩ | _ | _
  · simpa [reduceStmt, Stmt.typedDefinedVars] using (mapExpr_typed c).2.1
  all_goals simp [reduceStmt, Stmt.typedDefinedVars]

mutual
/-- Reducing a statement keeps its annotation check and its typed `init`s. -/
private theorem reduceStmt_typed : ∀ (s : Statement) (Γ : VarTyping Expression),
    Stmt.fvarTypesWellAnnotated Γ s → Stmt.initsTyped Expression.Typed s →
    Stmt.fvarTypesWellAnnotated Γ (reduceStmt s) ∧
      Stmt.initsTyped Expression.Typed (reduceStmt s)
  | .cmd c, Γ, hW, hT => by
    obtain ⟨hr, -, hi⟩ := mapExpr_typed c
    simp only [reduceStmt, Stmt.fvarTypesWellAnnotated, Stmt.initsTyped] at hW hT ⊢
    exact ⟨fun x ty h => hW x ty (hr h), hi hT⟩
  | .block l ss md, Γ, hW, hT => by
    simp only [reduceStmt, Stmt.fvarTypesWellAnnotated, Stmt.initsTyped] at hW hT ⊢
    exact reduceBlock_typed ss Γ hW hT
  | .ite (.det c) tss ess md, Γ, hW, hT => by
    simp only [reduceStmt, Stmt.fvarTypesWellAnnotated, Stmt.initsTyped,
      ExprOrNondet.getTypedVars] at hW hT ⊢
    obtain ⟨ht, ht'⟩ := reduceBlock_typed tss Γ hW.2.1 hT.1
    obtain ⟨he, he'⟩ := reduceBlock_typed ess Γ hW.2.2 hT.2
    exact ⟨⟨fun x ty h => hW.1 x ty (typedFvars_reduce c h), ht, he⟩, ht', he'⟩
  | .ite .nondet tss ess md, Γ, hW, hT => by
    simp only [reduceStmt, Stmt.fvarTypesWellAnnotated, Stmt.initsTyped] at hW hT ⊢
    obtain ⟨ht, ht'⟩ := reduceBlock_typed tss Γ hW.2.1 hT.1
    obtain ⟨he, he'⟩ := reduceBlock_typed ess Γ hW.2.2 hT.2
    exact ⟨⟨hW.1, ht, he⟩, ht', he'⟩
  | .loop g m inv body md, Γ, hW, hT => by
    have hb := reduceBlock_typed body Γ
    rcases g with g | _ <;> rcases m with _ | m <;>
      simp only [reduceStmt, Stmt.fvarTypesWellAnnotated, Stmt.initsTyped,
        ExprOrNondet.getTypedVars, Option.map_none, Option.map_some, Option.getD_none,
        Option.getD_some] at hW hT hb ⊢
    all_goals
      have hinv : Γ.annotates ((inv.map fun x => (x.1, reduceExpr x.2)).flatMap
          fun lp => HasFvars.getTypedFvars (P := Expression) lp.2) := fun x ty hx => by
        obtain ⟨lp, hlp, hx⟩ := List.mem_flatMap.1 hx
        obtain ⟨lp', hlp', rfl⟩ := List.mem_map.1 hlp
        exact hW.2.2.1 x ty (List.mem_flatMap.2 ⟨lp', hlp', typedFvars_reduce _ hx⟩)
      refine ⟨⟨?_, ?_, hinv, (hb hW.2.2.2 hT).1⟩, (hb hW.2.2.2 hT).2⟩
    all_goals first
      | exact fun x ty h => hW.1 x ty (typedFvars_reduce _ h)
      | exact hW.1
      | exact fun x ty h => hW.2.1 x ty (typedFvars_reduce _ h)
      | exact hW.2.1
  | .exit .., _, _, _ | .typeDecl .., _, _, _ => by
    simp [reduceStmt, Stmt.fvarTypesWellAnnotated, Stmt.initsTyped]

/-- Reducing a statement list keeps its annotation check and its typed `init`s. -/
private theorem reduceBlock_typed : ∀ (ss : Statements) (Γ : VarTyping Expression),
    Block.fvarTypesWellAnnotated Γ ss → Block.initsTyped Expression.Typed ss →
    Block.fvarTypesWellAnnotated Γ (reduceBlock ss) ∧
      Block.initsTyped Expression.Typed (reduceBlock ss)
  | [], _, _, _ => by simp [reduceBlock, Block.fvarTypesWellAnnotated, Block.initsTyped]
  | s :: ss, Γ, hW, hT => by
    simp only [reduceBlock, Block.fvarTypesWellAnnotated, Block.initsTyped] at hW hT ⊢
    rw [typedDefinedVars_reduceStmt]
    obtain ⟨h1, h2⟩ := reduceStmt_typed s Γ hW.1 hT.1
    obtain ⟨h3, h4⟩ := reduceBlock_typed ss _ hW.2 hT.2
    exact ⟨⟨h1, h3⟩, h2, h4⟩
end

/-- **Beta reduction keeps procedure bodies typed and def-use well formed.** Every procedure
    `q'` of `betaReduceProgram p` comes from a procedure `q` of `p` with the same header and
    metadata; when `q'` has a structured body, so has `q`, and the body of `q'` is def-use well
    formed for every defined-names and declared-functions predicates, passes the annotation check
    for every typing, and has typed `init`s, when the body of `q` does. -/
theorem betaReduceProgram_proc_typed {p : Program} {q' : Procedure} {md : MetaData Expression}
    (h : Decl.proc q' md ∈ (betaReduceProgram p).decls) :
    ∃ q, Decl.proc q md ∈ p.decls ∧ q'.header = q.header ∧
      ∀ ss' o, q'.body = .structured ss' o → ∃ ss, q.body = .structured ss o ∧
        (∀ D df, Block.defUseWellFormed D df ss = true →
          Block.defUseWellFormed D df ss' = true) ∧
        ∀ Γ, Block.fvarTypesWellAnnotated Γ ss → Block.initsTyped Expression.Typed ss →
          Block.fvarTypesWellAnnotated Γ ss' ∧ Block.initsTyped Expression.Typed ss' := by
  obtain ⟨_ | _ | _ | _ | _ | _ | _, hd, ⟨⟩⟩ := List.mem_map.1 h
  refine ⟨_, hd, rfl, fun ss' o hb => ?_⟩
  split at hb <;> cases hb
  exact ⟨_, ‹_›, fun D df => reduceBlock_defUse D df _, reduceBlock_typed _⟩

/-- Beta reduction keeps a statement list in passive form: it rewrites only expressions. -/
private theorem reduceBlock_passive (ss : Statements) (hp : Block.passiveForm ss = true) :
    Block.passiveForm (reduceBlock ss) = true := by
  induction ss using Block.passiveForm.induct <;> (try cases ‹ExprOrNondet Expression›) <;>
    simp_all [reduceBlock, reduceStmt, Command.mapExpr, Block.passiveForm]

/-- **Beta reduction keeps procedure bodies in passive form, typed and def-use well formed.**
    `betaReduceProgram_proc_typed`, and the body of `q'` is in passive form when that of `q`
    is. -/
theorem betaReduceProgram_proc_kept {p : Program} {q' : Procedure} {md : MetaData Expression}
    (h : Decl.proc q' md ∈ (betaReduceProgram p).decls) :
    ∃ q, Decl.proc q md ∈ p.decls ∧ q'.header = q.header ∧
      ∀ ss' o, q'.body = .structured ss' o → ∃ ss, q.body = .structured ss o ∧
        (Block.passiveForm ss = true → Block.passiveForm ss' = true) ∧
        (∀ D df, Block.defUseWellFormed D df ss = true →
          Block.defUseWellFormed D df ss' = true) ∧
        ∀ Γ, Block.fvarTypesWellAnnotated Γ ss → Block.initsTyped Expression.Typed ss →
          Block.fvarTypesWellAnnotated Γ ss' ∧ Block.initsTyped Expression.Typed ss' := by
  obtain ⟨_ | _ | _ | _ | _ | _ | _, hd, ⟨⟩⟩ := List.mem_map.1 h
  refine ⟨_, hd, rfl, fun ss' o hb => ?_⟩
  split at hb <;> cases hb
  exact ⟨_, ‹_›, reduceBlock_passive _, fun D df => reduceBlock_defUse D df _, reduceBlock_typed _⟩

end BetaReduce

end Core

end -- public section
