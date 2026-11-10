/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Simulation
public import Strata.DL.Imperative.CmdSemanticsProps
import Strata.Util.ExceptProps
import Strata.Util.OrderedSetProps

/-! # Properties of the simulation vocabulary

The variables a continuation reads (`mem_contFV`, `mem_contFV_cons`); reachability conditions
under store growth (`RE.Holds.mono`, `RE.Fails.mono`) and the value of their expressions
(`ev_REexpr_holds`); the scope after a list (`scopeAfter`); failing traces with the kind of their
failing event (`claimK_prepend`, `ClaimK.claim`, `Claim.kind`); the names a statement list
declares at any depth (`stmtsInits_mem_idents`, `wfl_inits_scope`); keys of hash maps built by
insertion (`foldr_insert_key`); and Boolean updates of value-valued stores
(`wfStore_update_bool`).

Key theorems: `ev_REexpr_holds`, `claimK_prepend`, `Claim.kind`, `wfl_inits_scope`.

Key definitions: `scopeAfter`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P]
  [iW : WPLang P] [iIL : WPIteLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iIL
omit iDE iB iLB iBo iFv iSu iId iLI iHa iFs iW iOp iLF iLFs iLV

variable {F : P.Factory} {c : P.Expr} {tss ess : PStmts P} {md : MetaData P} {s : PStmt P}
  {rest l : PStmts P} {k : List (PStmts P)} {x : P.Ident} {σ σ2 : SemanticStore P} {r : RE P}
  {t : AssertId P} {tr tr1 tr2 : List (Event P)} {ss : PStmts P} {b : Bool}

/-! ## Continuations, reachability conditions and kinds of failing traces -/

include iB iLB iFs iHa in
/-- The continuation reads `x` exactly when one of its statement lists does. -/
theorem mem_contFV : x ∈ contFV k ↔ ∃ l ∈ k, x ∈ Block.freeVars l := by
  simp [contFV, Strata.Util.OrderedSet.mem_eraseDups]

/-! ## Reachability conditions

Their truth under store growth, and the value of their expressions. -/

include iBo in
/-- A reachability condition that holds stays true as the store grows. -/
theorem RE.Holds.mono (h : r.Holds F σ)
    (hm : ∀ x v, σ x = some v → σ2 x = some v) : r.Holds F σ2 := by cases r <;> grind [RE.Holds]

include iBo in
/-- A false reachability condition stays false as the store grows. -/
theorem RE.Fails.mono (h : r.Fails F σ)
    (hm : ∀ x v, σ x = some v → σ2 x = some v) : r.Fails F σ2 := by
  cases r <;> grind [RE.Fails, Option.isSome_iff_exists]

include iBo in
/-- A reachability condition does not both hold and fail. -/
theorem RE.Holds.not_fails (h : r.Holds F σ) : ¬ r.Fails F σ := by
  cases r <;> grind [RE.Holds, RE.Fails, HasBool.ttVal_ne_ffVal]

include iDE iBo iFv iSu iFs iW iIL iOp iLF iLV in
omit iLV in
/-- The expression of a reachability condition that holds evaluates to `true`. -/
theorem ev_REexpr_holds (hF : WellFormedSemanticEvalBase F) {σ : SemanticStore P}
    (hC : WellFormedStore σ F) {r : RE P} (h : r.Holds F σ) :
    P.eval F σ r.expr = some (HasBool.ttVal F) := by
  have hb := HasBool.boolIsValOfTy (P := P) F
  cases r <;> grind [RE.Holds, RE.expr, notE, andE, hF.val.eval_tt, hF.val.eval_ff, ev_ite_true_b,
    ev_ite_false_b, ev_bvar hF.var hC]

/-! ## Scopes, continuations and traces

The scope after a list, the variables continuations read, and feasibility of traces. -/

/-- The scope after a statement list: its top-level locals are added. -/
@[expose] def scopeAfter : List P.Ident → (PStmts P) → List P.Ident
  | S, [] => S
  | S, s :: rest => scopeAfter (Stmt.topInits s ++ S) rest

/-- The scope after a list contains the scope before it. -/
theorem scopeAfter_sub : ∀ (S : List P.Ident) (L : (PStmts P)), S ⊆ scopeAfter S L :=
  fun S L => by induction L generalizing S <;> grind [scopeAfter, List.Subset]

include iB iLB iFs iHa in
/-- The continuation `l :: k` reads `x` exactly when `l` or `k` does. -/
theorem mem_contFV_cons : x ∈ contFV (l :: k) ↔
    x ∈ Block.freeVars l ∨ x ∈ contFV k := by simp [mem_contFV]

include iB iLB iFs iHa in
/-- A continuation reads what its tail reads. -/
theorem contFV_tail_sub : contFV k ⊆ contFV (l :: k) := fun _ hx => mem_contFV_cons.2 (.inr hx)

include iBo in
/-- A feasible prefix keeps a failing feasible trace failing, feasible and of its kind. -/
theorem claimK_prepend {e : P.Expr} (h1 : Trace.AssumptionsHold P evalInterp () tr1)
    (h2 : ClaimK b t e tr2) : ClaimK b t e (tr1 ++ tr2) :=
  match h2 with
  | ⟨evs, a, htr, hf, ht, he⟩ =>
    ⟨tr1 ++ evs, a, by simp [htr], Trace.AssumptionsHold.append h1 hf, ht, he⟩

include iBo in
/-- A trace claiming a failure at an event of some kind with the condition `e` claims the failure
    with the condition `e`. -/
theorem ClaimK.claim {e : P.Expr} (h : ClaimK b t e tr) : Claim t e tr :=
  match h with | ⟨evs, _, htr, hf, ht, _⟩ => ⟨evs, _, htr, hf, ht⟩

include iBo in
/-- A trace claiming a failure with the condition `e` claims it at an event of some kind. -/
theorem _root_.Imperative.BigStep.Claim.kind {e : P.Expr} (h : Claim t e tr) :
    ∃ b, ClaimK b t e tr := by
  obtain ⟨evs, ev, rfl, hf, ht⟩ := h
  cases ev with
  | assert a => exact ⟨false, evs, a, rfl, hf, ht, ht.2.2.1⟩
  | cover a => exact ⟨true, evs, a, rfl, hf, ht, ht.2.2.1⟩
  | assume => exact ht.elim

/-! ## Statement lists

The variables a statement list reads include those of its head. -/

include iB iFs iLB iHa in
/-- A statement list reads what its head statement reads. -/
theorem Block.freeVars_cons_sub : ∀ x ∈ Stmt.freeVars s, x ∈ Block.freeVars (s :: rest) := by
  rcases s with ⟨⟨_, _, _ | _, _⟩ | _⟩ | _ <;> grind [Block.freeVars, Stmt.freeVars]

/-! ## `ite`

The variables of an `ite`'s condition are read by its continuation. -/

include iB iLB iFs iHa in
/-- The continuation of an `ite` reads the variables of its condition. -/
theorem ite_cond_fv : ∀ x ∈ exprFV c, x ∈ contFV ((.ite (.det c) tss ess md :: rest) :: k) :=
  fun _ hx => mem_contFV_cons.2 (.inl (by simp [Block.freeVars, Stmt.freeVars, hx]))

/-! ## Declarations of statement lists

The names a statement list declares at any depth (`stmtsInits`) occur in it, and a well-scoped
list declares only loop-free locals outside its scope. -/

/-- The names a statement list declares at any depth are those of its head followed by those of
    its rest. -/
theorem stmtsInits_cons_eq (s : PStmt P) (rest : PStmts P) :
    stmtsInits (s :: rest) = stmtsInits [s] ++ stmtsInits rest := by
  rcases s with ((_ | _ | _ | _ | _) | _) | _ <;> simp [stmtsInits]

include iFs in
/-- Every name a statement list declares at any depth occurs among its identifiers. -/
theorem stmtsInits_mem_idents : ∀ x ∈ stmtsInits ss, x ∈ Block.idents ss := by
  induction ss using stmtsInits.induct <;> intro x hx <;> (try cases ‹ExprOrNondet P›) <;>
    grind [stmtsInits, Block.idents, Stmt.idents]

include iB iFs iLB iHa in
/-- A name a list well scoped from `S` (`Block.WellScoped`) declares at any depth is a loop-free
    local (in `Lc`) occurring in the list and not in `S`. -/
theorem wfl_inits_scope {Lc : List P.Ident} (ss : PStmts P) :
    ∀ {S : List P.Ident}, Block.WellScoped Lc S ss → ∀ {x},
        x ∈ stmtsInits ss → x ∈ Lc ∧ x ∈ Block.idents ss ∧ x ∉ S := by
  induction ss using stmtsInits.induct <;> intro S h x hx <;> (try cases ‹ExprOrNondet P›) <;>
    grind [Block.WellScoped, Stmt.WellScoped, stmtsInits, stmtsInits_mem_idents]

include iB iFs iLB iHa in
/-- A list well scoped from `S` declares no name of `S`, at any depth. -/
theorem wfl_inits_disjoint {Lc : List P.Ident} (S : List P.Ident) (ss : PStmts P)
    (h : Block.WellScoped Lc S ss) : ∀ z ∈ S, z ∉ stmtsInits ss :=
  fun _ hz hi => (wfl_inits_scope ss h hi).2.2 hz

/-! ## Hash maps built by insertion -/

/-- A key of the hash map that inserts the pairs of `l` from the last one to the first is the
    first component of a pair of `l`. -/
theorem foldr_insert_key {α β : Type _} [BEq α] [Hashable α] [LawfulBEq α] (l : List (α × β))
    (n : α) (h : ((l.foldr (fun x m => m.insert x.1 x.2) {} : Std.HashMap α β)[n]?).isSome) :
    ∃ p ∈ l, p.1 = n := by
  induction l <;> grind

/-! ## Value-valued stores -/

include iDE iBo iFs iLV in
omit iFs in
/-- Updating a name of a value-valued store to a Boolean (`tt` or `ff`) keeps it
    value-valued. -/
theorem wfStore_update_bool (hC : WellFormedStore σ F) (x : P.Ident) {b : P.Val}
    (hb : b = HasBool.ttVal F ∨ b = HasBool.ffVal F) :
    WellFormedStore (SemanticStore.update σ x b) F :=
  wfStore_update hC x (hb.elim (· ▸ (HasBool.boolIsVal F).1) (· ▸ (HasBool.boolIsVal F).2))

end -- public section

end WP
end Imperative
