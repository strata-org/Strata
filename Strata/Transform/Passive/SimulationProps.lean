/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Simulation
import Strata.Util.ExceptProps

/-! # Properties of well-scopedness and failing traces

A list that passes the Boolean check `wflB` is well scoped (`wflB_wfl`); the one-pass hash-set
check `wflBH` computes `wflB` (`wflBH_eq`); and a feasible prefix keeps a failing feasible trace
failing (`claim_prepend`).

Key theorems: `wflB_wfl`, `wflBH_eq`, `claim_prepend`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iDE iB iLB iBo iFv iSu iId iLI iHa iFs iW iOp iLF iLFs iLV

variable {F : P.Factory} {c : P.Expr} {tss ess : PStmts P} {md : MetaData P} {s : PStmt P}
  {rest l : PStmts P} {k : List (PStmts P)} {x : P.Ident} {σ σ2 : SemanticStore P} {r : RE P}
  {t : AssertId P} {tr1 tr2 : List (Event P)} {ss : PStmts P}

/-! ## The well-scopedness check -/

include iB iFs in
/-- A statement list that passes the well-scopedness check `wflB` is well scoped (`WFL`). -/
theorem wflB_wfl [LawfulBEq P.Ident] [Hashable P.Ident] {Lc : List P.Ident} :
    ∀ {S : List P.Ident} {ss : PStmts P}, wflB Lc S ss = true → WFL Lc S ss := by
  intro S ss h
  induction S, ss using wflB.induct (motive_2 := fun S s => wfs1B Lc S s = true → WFS1 Lc S s) <;>
    grind [wflB, wfs1B, WFL, WFS1]

include iB iLB iHa in
/-- Declaring the names of `S` in order represents `S`. -/
private theorem ScopeCountRep.ofList (S : List P.Ident) :
    ScopeCountRep (S.foldl ScopeCount.inc {}) S := by
  suffices h : ∀ T (b : ScopeCount P), ScopeCountRep b T →
      ScopeCountRep (S.foldl ScopeCount.inc b) (S.reverse ++ T) by
    simpa [ScopeCountRep] using h [] {} fun x => by simp
  induction S <;> grind [ScopeCountRep.inc]

include iDE iB iLB iHa iFs in
/-- The hash-set walks agree with the Boolean checks on a scope hash map representing the scope
    list `T`: `wflList`, `wflGo`, `wflStmt` succeed exactly when `wflB`, `wflB`, `wfs1B` hold,
    and their results represent the scope list after the walk. -/
private theorem wflList_spec (Lc : List P.Ident) (lc : Std.HashSet P.Ident)
    (hlc : ∀ x, lc.contains x = Lc.contains x) :
    (∀ b ss, ∀ T, ScopeCountRep b T → (wflList lc b ss).isSome = wflB Lc T ss ∧
      ∀ b', wflList lc b ss = some b' → ScopeCountRep b' T) ∧
    (∀ b a ss, ∀ T, ScopeCountRep b T → (wflGo lc b a ss).isSome = wflB Lc T ss ∧
      ∀ b' a', wflGo lc b a ss = some (b', a') → ∃ d, a' = d ++ a ∧ ScopeCountRep b' (d ++ T)) ∧
    (∀ b s, ∀ T, ScopeCountRep b T → (∀ x ty e md, s = .cmd (.cmd (.init x ty e md)) → False) →
      (wflStmt lc b s).isSome = wfs1B Lc T s ∧
        ∀ b', wflStmt lc b s = some b' → ScopeCountRep b' T) := by
  apply wflList.mutual_induct lc <;> intros
  all_goals try grind [‹ScopeCountRep _ _›.contains_eq, wflList, wflGo, wflStmt, wflB, wfs1B,
    topInit,
    ScopeCountRep.decs, ScopeCountRep.inc]
  all_goals simp_all [wflGo, wflStmt, wflB, wfs1B]

include iDE iB iLB iHa iFs in
/-- `wflBH` computes `wflB`, linearly where `wflB` looks names up in the scope and locals
    lists. -/
theorem wflBH_eq (Lc S : List P.Ident) (ss : PStmts P) : wflBH Lc S ss = wflB Lc S ss :=
  ((wflList_spec Lc _ fun _ => Std.HashSet.contains_ofList).1 _ ss S (ScopeCountRep.ofList S)).1

/-! ## Feasibility of traces -/

include iBo in
/-- A feasible prefix keeps a failing feasible trace failing and feasible. -/
theorem claim_prepend (h1 : Trace.AssumptionsHold P evalInterp () tr1)
    (h2 : Claim t tr2) : Claim t (tr1 ++ tr2) :=
  match h2 with
  | ⟨evs, e, htr, hf, ht⟩ => ⟨tr1 ++ evs, e, by simp [htr], Trace.AssumptionsHold.append h1 hf, ht⟩

end -- public section

end WP
end Imperative
