/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.StmtShape
public import Strata.Transform.Simplify.LiveSweep
public import Strata.Languages.Core.StatementProps
import all Strata.Transform.Simplify
import Strata.DL.Imperative.StmtProps
import Strata.DL.Imperative.CmdProps

/-! # Simplify: the shape of the dead-definition sweep

Facts about `dropDeadDefsAux` and its helpers that do not depend on how expressions are
evaluated: the sweep at each shape of statement, what the definitely-defined map
`Defined` records, what a compound statement
reads and writes, and that the sweep only ever adds live names.

## Key results

* `dropDeadDefsAux_nil`, `dropDeadDefsAux_cons_dead`, `dropDeadDefsAux_cons_keep` and the
  `dropDeadDefsStmt_*` equations: the sweep at each shape; `keep_of_not_dead` decides
  between the dead and the kept case, and `dropDeadDefsAux_singleton_keep` is the kept
  case for a one-statement list.
* `Defined.ofParams_spec` and `init_of_definedBy`: what the sweep may assume defined,
  and what it may drop.
* `live_dropDeadDefsAux_mono`: a name live after a swept list is live before it, with
  `live_dropDeadDefsStmt_mono` and `live_dropDeadDefsArms_mono` its statement and branch
  cases.
* `mem_dropDeadDefsAux_live` and `mem_dropDeadDefsStmt_live`: the live set before a swept
  list holds exactly the names live after it and those the kept statements read or write;
  `dropDeadDefsAux_cons_keep_live` and `live_dropDeadDefsAux` restate it.
* `dropDeadDefsStmt_ite_arms`: a branch's arms are swept as if each were swept on its own.
-/

public section

namespace Core.Simplify

open Lambda Imperative

variable {F : Lambda.Factory CoreLParams} {D : Defined}

/-! ## Live sets

The sweep carries liveness as a `Std.HashSet String` of names; `Live` reads such a set
as a predicate on identifiers. -/

/-- `x` is live according to the name set `L`. -/
@[expose] def Live (L : Std.HashSet String) (x : CoreIdent) : Prop :=
  L.contains x.name = true

/-- Inserting a name keeps every live variable live. -/
theorem Live.insert {L : Std.HashSet String} {n : String} {x : CoreIdent}
    (h : Live L x) : Live (L.insert n) x := by
  simp only [Live, Std.HashSet.contains_insert] at h ⊢
  simp [h]

/-- The inserted name is live. -/
theorem Live.insert_self (L : Std.HashSet String) (x : CoreIdent) :
    Live (L.insert x.name) x := by
  simp only [Live, Std.HashSet.contains_insert, BEq.rfl, Bool.true_or]

/-- A name live after an insertion is live before it or is the name inserted. -/
theorem live_insert_inv {L : Std.HashSet String} {n : String} {x : CoreIdent}
    (h : Live (L.insert n) x) : Live L x ∨ x.name = n := by
  simp only [Live, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact .inr h.symm
  · exact .inl h

/-- Folding a list into a live set keeps every live variable live. The names folded in
    are read off the list by `f`. -/
theorem Live.foldl {α : Type} {f : α → String} {L : Std.HashSet String} {xs : List α}
    {x : CoreIdent} (h : Live L x) : Live (xs.foldl (fun l y => l.insert (f y)) L) x := by
  induction xs generalizing L with
  | nil => exact h
  | cons y ys ih => exact ih h.insert

/-- Every name folded into a live set is live in the result. -/
theorem Live.foldl_mem {α : Type} {f : α → String} {L : Std.HashSet String}
    {xs : List α} {x : CoreIdent} (h : x.name ∈ xs.map f) :
    Live (xs.foldl (fun l y => l.insert (f y)) L) x := by
  induction xs generalizing L with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.map_cons, List.mem_cons] at h
    rcases h with heq | hx
    · rw [List.foldl_cons, ← heq]
      exact Live.foldl (L := L.insert x.name) (xs := ys) (Live.insert_self L x)
    · exact ih hx

/-- A name live after folding in a list is live before the fold or one of the names
    folded in. -/
theorem live_foldl_inv {L : Std.HashSet String} {xs : List CoreIdent} {x : CoreIdent}
    (h : Live (xs.foldl (fun l y => l.insert y.name) L) x) : Live L x ∨ x ∈ xs := by
  induction xs generalizing L with
  | nil => exact .inl h
  | cons y ys ih =>
    rw [List.foldl_cons] at h
    rcases ih h with h' | hmem
    · rcases live_insert_inv h' with h'' | h''
      · exact .inl h''
      · exact .inr (coreIdent_eq_of_name h'' ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ hmem)

/-- `x` is live in `L` exactly when its name is a member. -/
theorem live_iff_mem {L : Std.HashSet String} {x : CoreIdent} : Live L x ↔ x.name ∈ L :=
  Std.HashSet.mem_iff_contains.symm

/-- `insertTracked` keeps every live variable live. -/
theorem live_insertTracked {L : Std.HashSet String} {added ys : List String} {x : CoreIdent}
    (h : Live L x) : Live (insertTracked L added ys).1 x :=
  live_iff_mem.mpr ((insertTracked_mem L added ys x.name).mpr (.inl (live_iff_mem.mp h)))

/-- Every name `insertTracked` is given is live in the result. -/
theorem live_insertTracked_of_mem {L : Std.HashSet String} {added ys : List String}
    {x : CoreIdent} (h : x.name ∈ ys) : Live (insertTracked L added ys).1 x :=
  live_iff_mem.mpr ((insertTracked_mem L added ys x.name).mpr (.inr h))

/-- Erasing names keeps live every live variable it does not name. -/
theorem Live.erase_foldl {L : Std.HashSet String} {ns : List String} {x : CoreIdent}
    (h : Live L x) (hx : x.name ∉ ns) : Live (ns.foldl (·.erase ·) L) x := by
  induction ns generalizing L with
  | nil => exact h
  | cons n ns ih =>
    rw [List.foldl_cons]
    refine ih ?_ (fun hm => hx (List.mem_cons_of_mem _ hm))
    simp only [Live, Std.HashSet.contains_erase, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, beq_eq_false_iff_ne] at h ⊢
    exact ⟨fun he => hx (he ▸ List.mem_cons_self), h⟩

/-! ## Definitely-defined variables -/

/-- The definitely-defined variables after a statement that is not a deterministic
    `init` are those before it. -/
theorem Defined.after_of_not_init {D : Defined} {s : Statement}
    (h : ∀ x ty e md, s ≠ Statement.init x ty (.det e) md) : D.after s = D := by
  unfold Defined.after
  split
  next x ty e md => exact absurd rfl (h x ty e md)
  next => rfl

/-- A deterministic `init` records its variable at its declared type. -/
theorem Defined.after_init (D : Defined) (x : CoreIdent) (ty : Expression.Ty)
    (e : Expression.Expr) (md : MetaData Expression) :
    D.after (Statement.init x ty (.det e) md) = D.insert x.name ty := by
  unfold Defined.after; rfl

/-- Recording a variable keeps every other variable's entry. -/
theorem Defined.insert_ne {D : Defined} {x y : CoreIdent} {ty : Expression.Ty}
    (h : x ≠ y) : (D.insert x.name ty)[y.name]? = D[y.name]? := by
  rw [Std.HashMap.getElem?_insert]
  split
  · rename_i hxy
    exact absurd (coreIdent_eq_of_name (by simpa using hxy)) h
  · rfl

/-- What the fold behind `Defined.ofParams` records comes from the map it starts from, or
    from an input parameter whose name is not written. -/
private theorem ofParams_foldl {written : Std.HashSet String} :
    ∀ (inputs : List (CoreIdent × Lambda.LMonoTy)) (acc : Defined) (k : String)
      (ty : Expression.Ty),
    (inputs.foldl (fun (D : Defined) (p : CoreIdent × Lambda.LMonoTy) =>
        if written.contains p.1.name then D else D.insert p.1.name (.forAll [] p.2))
        acc)[k]? = some ty →
    acc[k]? = some ty ∨ ∃ x t, (x, t) ∈ inputs ∧ x.name = k ∧ ty = .forAll [] t ∧
      written.contains k = false := by
  intro inputs
  induction inputs with
  | nil => intro acc k ty h; exact .inl h
  | cons p rest ih =>
    intro acc k ty h
    rw [List.foldl_cons] at h
    rcases ih _ k ty h with h' | ⟨x, t, hmem, hx, hty, hw⟩
    · by_cases hc : written.contains p.1.name = true
      · simp only [hc, ↓reduceIte] at h'; exact .inl h'
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h'
        rw [Std.HashMap.getElem?_insert] at h'
        split at h'
        next heq =>
          cases h'
          have hk : p.1.name = k := by simpa using heq
          refine .inr ⟨p.1, p.2, by simp, hk, rfl, ?_⟩
          rw [← hk]
          simpa using hc
        next => exact .inl h'
    · exact .inr ⟨x, t, List.mem_cons_of_mem _ hmem, hx, hty, hw⟩

/-- **What `Defined.ofParams` records** is an input parameter, at its declared type, that
    the body does not write. -/
theorem Defined.ofParams_spec {inputs : @Lambda.LMonoTySignature Unit} {ss : List Statement}
    {y : CoreIdent} {ty : Expression.Ty} (h : (Defined.ofParams inputs ss)[y.name]? = some ty) :
    (∃ t, (y, t) ∈ ListMap.toList inputs ∧ ty = .forAll [] t) ∧
      y ∉ Block.modifiedOrDefinedVars (P := Expression) (C := Command) ss false := by
  unfold Defined.ofParams at h
  rcases ofParams_foldl _ _ _ _ h with h' | ⟨x, t, hmem, hx, hty, hw⟩
  · simp at h'
  · have hxy : x = y := coreIdent_eq_of_name hx
    subst hxy
    refine ⟨⟨t, hmem, hty⟩, fun hin => ?_⟩
    have hlive := (mem_insertNames (names := ∅)).mpr (.inr (List.mem_map_of_mem hin))
    rw [Std.HashSet.mem_iff_contains, hw] at hlive
    cases hlive

/-- What the sweep may drop is a deterministic `init` whose right-hand side surely
    evaluates. -/
theorem init_of_definedBy {s : Statement} {x : CoreIdent} (h : definedBy F D s = some x) :
    ∃ ty e md, s = Statement.init x ty (.det e) md ∧ surelyEvaluates F D ty e = true := by
  unfold definedBy at h
  split at h
  next y ty e md =>
    split at h
    next hs => cases h; exact ⟨ty, e, md, rfl, hs⟩
    next => cases h
  next => cases h

/-! ## Reads and writes of a compound statement -/

/-- A variable a block's body reads is read by the block. -/
theorem mem_getVars_block {l : String} {ss : List Statement} {md : MetaData Expression}
    {x : CoreIdent} (h : x ∈ Block.getVars ss) : x ∈ Stmt.getVars (.block l ss md) := by
  rw [Stmt.getVars]; exact h

/-- A variable a block's body writes is written by the block. -/
theorem mem_modOrDef_block {l : String} {ss : List Statement} {md : MetaData Expression}
    {x : CoreIdent}
    (h : x ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command) ss false) :
    x ∈ Stmt.modifiedOrDefinedVars (P := Expression) (C := Command) (.block l ss md) false := by
  simpa using h

/-- A free variable of the guard is read by the conditional. -/
theorem mem_getVars_iteCond {cond : Expression.Expr} {ts es : List Statement}
    {md : MetaData Expression} {x : CoreIdent}
    (h : x ∈ HasFvars.getFvars (P := Expression) cond) :
    x ∈ Stmt.getVars (.ite (.det cond) ts es md) := by
  rw [Stmt.getVars, ExprOrNondet.getVars_det, List.append_assoc]
  exact List.mem_append_left _ h

/-- A variable the then-arm reads is read by the conditional. -/
theorem mem_getVars_iteThen {c : ExprOrNondet Expression} {ts es : List Statement}
    {md : MetaData Expression} {x : CoreIdent} (h : x ∈ Block.getVars ts) :
    x ∈ Stmt.getVars (.ite c ts es md) := by
  rw [Stmt.getVars]
  simp only [List.mem_append]
  exact .inl (.inr h)

/-- A variable the else-arm reads is read by the conditional. -/
theorem mem_getVars_iteElse {c : ExprOrNondet Expression} {ts es : List Statement}
    {md : MetaData Expression} {x : CoreIdent} (h : x ∈ Block.getVars es) :
    x ∈ Stmt.getVars (.ite c ts es md) := by
  rw [Stmt.getVars]
  simp only [List.mem_append]
  exact .inr h

/-- A variable the then-arm writes is written by the conditional. -/
theorem mem_modOrDef_iteThen {c : ExprOrNondet Expression} {ts es : List Statement}
    {md : MetaData Expression} {x : CoreIdent}
    (h : x ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command) ts false) :
    x ∈ Stmt.modifiedOrDefinedVars (P := Expression) (C := Command) (.ite c ts es md) false :=
  mem_writes_ite_arm (b := true) h

/-- A variable the else-arm writes is written by the conditional. -/
theorem mem_modOrDef_iteElse {c : ExprOrNondet Expression} {ts es : List Statement}
    {md : MetaData Expression} {x : CoreIdent}
    (h : x ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command) es false) :
    x ∈ Stmt.modifiedOrDefinedVars (P := Expression) (C := Command) (.ite c ts es md) false :=
  mem_writes_ite_arm (b := false) h

/-- A free variable of the loop guard is read by the loop. -/
theorem mem_getVars_loopGuard {g : Expression.Expr} {m : Option Expression.Expr}
    {invs : List (String × Expression.Expr)} {body : List Statement}
    {md : MetaData Expression} {x : CoreIdent}
    (h : x ∈ HasFvars.getFvars (P := Expression) g) :
    x ∈ Stmt.getVars (.loop (.det g) m invs body md) := by
  rw [Stmt.getVars, ExprOrNondet.getVars_det]
  simp only [List.mem_append]
  exact .inl (.inl (.inl h))

/-- A variable the loop body reads is read by the loop. -/
theorem mem_getVars_loopBody {g : ExprOrNondet Expression} {m : Option Expression.Expr}
    {invs : List (String × Expression.Expr)} {body : List Statement}
    {md : MetaData Expression} {x : CoreIdent} (h : x ∈ Block.getVars body) :
    x ∈ Stmt.getVars (.loop g m invs body md) := by
  rw [Stmt.getVars]
  exact List.mem_append_right _ h

/-- A variable the loop body writes is written by the loop. -/
theorem mem_modOrDef_loopBody {g : ExprOrNondet Expression} {m : Option Expression.Expr}
    {invs : List (String × Expression.Expr)} {body : List Statement}
    {md : MetaData Expression} {x : CoreIdent}
    (h : x ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command) body false) :
    x ∈ Stmt.modifiedOrDefinedVars (P := Expression) (C := Command)
      (.loop g m invs body md) false := by
  simpa using h

/-! ## The sweep at each shape

The sweep returns the swept statements, the names live before them, and `added`; the
equations are stated on those projections. -/

/-- The live set in force before a kept statement `s'`: the names live after it, plus
    what it reads and what it writes. -/
def liveBefore (live : Std.HashSet String) (s' : Statement) : Std.HashSet String :=
  (Stmt.modifiedOrDefinedVars s' (excludeScoped := false)).foldl
    (fun l y => l.insert y.name)
    ((Stmt.getVars s').foldl (fun l y => l.insert y.name) live)

/-- The sweep of the empty list drops nothing and leaves the live set alone. -/
theorem dropDeadDefsAux_nil (L : Std.HashSet String) (added : List String) :
    dropDeadDefsAux F D L added [] = ([], L, added) := by
  rw [dropDeadDefsAux]

/-- A statement defining a variable nothing downstream mentions disappears, and the
    sweep is that of the rest, swept knowing what the statement defines. -/
theorem dropDeadDefsAux_cons_dead {L : Std.HashSet String} {added : List String}
    {s : Statement} {rest : List Statement} {x : CoreIdent} (hdef : definedBy F D s = some x)
    (hdead : (dropDeadDefsAux F (D.after s) L added rest).2.1.contains x.name = false) :
    dropDeadDefsAux F D L added (s :: rest) = dropDeadDefsAux F (D.after s) L added rest := by
  rcases hr : dropDeadDefsAux F (D.after s) L added rest with ⟨r₁, r₂, r₃⟩
  rw [hr] at hdead
  rw [dropDeadDefsAux, hr]
  simp only at hdead ⊢
  simp [hdef, hdead]

/-- A statement that defines nothing the sweep may drop, or whose defined variable is live
    after it, is kept and swept with what is live after it. -/
theorem dropDeadDefsAux_cons_keep {L : Std.HashSet String} {added : List String}
    {s : Statement} {rest : List Statement}
    (hkeep : ∀ x, definedBy F D s = some x →
      (dropDeadDefsAux F (D.after s) L added rest).2.1.contains x.name = true) :
    dropDeadDefsAux F D L added (s :: rest) =
      let r := dropDeadDefsAux F (D.after s) L added rest
      let t := dropDeadDefsStmt F D r.2.1 r.2.2 s
      (t.1 :: r.1, t.2.1, t.2.2) := by
  rcases hr : dropDeadDefsAux F (D.after s) L added rest with ⟨r₁, r₂, r₃⟩
  rw [hr] at hkeep
  rw [dropDeadDefsAux, hr]
  simp only at hkeep ⊢
  cases hdef : definedBy F D s with
  | none => simp
  | some x => simp [hkeep x hdef]

/-- Whether the sweep keeps `s` is decided by whether what it defines is live after it. -/
theorem keep_of_not_dead {L : Std.HashSet String} {added : List String} {s : Statement}
    {rest : List Statement}
    (hdead : ¬ ∃ x, definedBy F D s = some x ∧
      (dropDeadDefsAux F (D.after s) L added rest).2.1.contains x.name = false) :
    ∀ x, definedBy F D s = some x →
      (dropDeadDefsAux F (D.after s) L added rest).2.1.contains x.name = true := by
  intro x hdef
  by_cases hb : (dropDeadDefsAux F (D.after s) L added rest).2.1.contains x.name = true
  · exact hb
  · exact absurd ⟨x, hdef, by simpa using hb⟩ hdead

/-- A statement that defines nothing the sweep may drop is kept and swept. -/
theorem dropDeadDefsAux_singleton_keep (L : Std.HashSet String) (added : List String)
    {s : Statement} (hdef : definedBy F D s = none) :
    dropDeadDefsAux F D L added [s] =
      ([(dropDeadDefsStmt F D L added s).1], (dropDeadDefsStmt F D L added s).2.1,
        (dropDeadDefsStmt F D L added s).2.2) := by
  have hkeep : ∀ x, definedBy F D s = some x →
      (dropDeadDefsAux F (D.after s) L added ([] : List Statement)).2.1.contains x.name =
        true := by
    intro x hx; rw [hdef] at hx; cases hx
  rw [dropDeadDefsAux_cons_keep hkeep, dropDeadDefsAux_nil]

/-- A command is left alone, and what it reads and writes becomes live. -/
theorem dropDeadDefsStmt_cmd (live : Std.HashSet String) (added : List String) (c : Command) :
    dropDeadDefsStmt F D live added (.cmd c) =
      (.cmd c, insertTracked live added ((Stmt.getVars (.cmd c : Statement) ++
        Stmt.modifiedOrDefinedVars (.cmd c : Statement) (excludeScoped := false)).map
          (·.name))) := by
  unfold dropDeadDefsStmt; rfl

/-- A block's body is swept with what is live after the block. -/
theorem dropDeadDefsStmt_block (live : Std.HashSet String) (added : List String) (l : String)
    (ss : List Statement) (md : MetaData Expression) :
    dropDeadDefsStmt F D live added (.block l ss md) =
      (.block l (dropDeadDefsAux F D live added ss).1 md,
        (dropDeadDefsAux F D live added ss).2.1, (dropDeadDefsAux F D live added ss).2.2) := by
  rw [dropDeadDefsStmt]

/-- A conditional's arms are swept by `dropDeadDefsArms`, the one with fewer statements
    first, and its guard's variables become live. -/
theorem dropDeadDefsStmt_ite (live : Std.HashSet String) (added : List String)
    (c : ExprOrNondet Expression) (ts es : List Statement) (md : MetaData Expression) :
    dropDeadDefsStmt F D live added (.ite c ts es md) =
      if fewerStmts es ts then
        let r := dropDeadDefsArms F D live added es ts
        let t := insertTracked r.2.2.1 r.2.2.2 (c.getVars.map (·.name))
        (.ite c r.2.1 r.1 md, t.1, t.2)
      else
        let r := dropDeadDefsArms F D live added ts es
        let t := insertTracked r.2.2.1 r.2.2.2 (c.getVars.map (·.name))
        (.ite c r.1 r.2.1 md, t.1, t.2) := by
  rw [dropDeadDefsStmt]
  by_cases h : fewerStmts es ts = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true]

/-- A loop's body is swept with what is live after the loop, and the variables of its
    guard, measure and invariants become live. -/
theorem dropDeadDefsStmt_loop (live : Std.HashSet String) (added : List String)
    (g : ExprOrNondet Expression) (m : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (body : List Statement)
    (md : MetaData Expression) :
    dropDeadDefsStmt F D live added (.loop g m invs body md) =
      let r := dropDeadDefsAux F D live added body
      let t := insertTracked r.2.1 r.2.2
        ((Stmt.getVars (.loop g m invs [] md : Statement)).map (·.name))
      (.loop g m invs r.1 md, t.1, t.2) := by
  rw [dropDeadDefsStmt]

/-- An `exit` is left alone and makes nothing live. -/
theorem dropDeadDefsStmt_exit (live : Std.HashSet String) (added : List String) (l : String)
    (md : MetaData Expression) :
    dropDeadDefsStmt F D live added (.exit l md) = (.exit l md, live, added) := by
  unfold dropDeadDefsStmt; rfl

/-- A type declaration is left alone and makes nothing live. -/
theorem dropDeadDefsStmt_typeDecl (live : Std.HashSet String) (added : List String)
    (tc : TypeConstructor) (md : MetaData Expression) :
    dropDeadDefsStmt F D live added (Statement.typeDecl tc md) =
      (Statement.typeDecl tc md, live, added) := by
  unfold dropDeadDefsStmt; rfl

/-! ## The sweep only adds live names -/

mutual

/-- Sweeping a statement keeps every name live after it live before it. -/
theorem live_dropDeadDefsStmt_mono (D : Defined) (live : Std.HashSet String)
    (added : List String) (stmt : Statement) {x : CoreIdent} (h : Live live x) :
    Live (dropDeadDefsStmt F D live added stmt).2.1 x := by
  match stmt with
  | .ite c ts es md =>
    rw [dropDeadDefsStmt_ite]
    split
    · exact live_insertTracked (live_dropDeadDefsArms_mono D live added es ts h)
    · exact live_insertTracked (live_dropDeadDefsArms_mono D live added ts es h)
  | .block l ss md =>
    rw [dropDeadDefsStmt_block]
    exact live_dropDeadDefsAux_mono D live added ss h
  | .loop g m invs body md =>
    rw [dropDeadDefsStmt_loop]
    exact live_insertTracked (live_dropDeadDefsAux_mono D live added body h)
  | .cmd c => rw [dropDeadDefsStmt_cmd]; exact live_insertTracked h
  | .exit l md => rw [dropDeadDefsStmt_exit]; exact h
  | .typeDecl tc md => rw [dropDeadDefsStmt_typeDecl]; exact h
  termination_by sizeOf stmt

/-- Sweeping the two arms of a branch keeps every name live after it live before it. -/
theorem live_dropDeadDefsArms_mono (D : Defined) (live : Std.HashSet String)
    (added : List String) (first second : List Statement) {x : CoreIdent}
    (h : Live live x) : Live (dropDeadDefsArms F D live added first second).2.2.1 x := by
  rw [dropDeadDefsArms]
  split
  · exact live_dropDeadDefsAux_mono D live added second h
  · simp only
    by_cases hx : x.name ∈ (dropDeadDefsAux F D live [] first).2.2
    · exact live_insertTracked_of_mem hx
    · exact live_insertTracked (live_dropDeadDefsAux_mono D _ added second
        (Live.erase_foldl (live_dropDeadDefsAux_mono D live [] first h) hx))
  termination_by sizeOf first + sizeOf second
  decreasing_by all_goals (cases first <;> cases second <;> simp <;> omega)

/-- **The live set only grows as the sweep goes backwards**: a name live after a swept
    list is live before it. -/
theorem live_dropDeadDefsAux_mono (D : Defined) (L : Std.HashSet String)
    (added : List String) (ss : List Statement) {x : CoreIdent} (h : Live L x) :
    Live (dropDeadDefsAux F D L added ss).2.1 x := by
  match ss with
  | [] => rw [dropDeadDefsAux_nil]; exact h
  | s :: rest =>
    have ih := live_dropDeadDefsAux_mono (D.after s) L added rest h
    by_cases hdead : ∃ y, definedBy F D s = some y ∧
        (dropDeadDefsAux F (D.after s) L added rest).2.1.contains y.name = false
    · obtain ⟨y, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse]
      exact ih
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)]
      exact live_dropDeadDefsStmt_mono D _ _ s ih
  termination_by sizeOf ss

end

/-! ## The live set the sweep returns

The live set before a swept statement or list holds exactly the names live after it and
the names the swept statements read or write. -/

/-- The names `liveBefore` adds are what the statement reads and writes. -/
theorem mem_liveBefore {live : Std.HashSet String} {s' : Statement} {n : String} :
    n ∈ liveBefore live s' ↔ n ∈ live ∨ n ∈ (Stmt.getVars s').map (·.name) ∨
      n ∈ (Stmt.modifiedOrDefinedVars s' false).map (·.name) := by
  unfold liveBefore
  rw [← insertNames, mem_insertNames, ← insertNames, mem_insertNames, or_assoc]

mutual

/-- The live set before a swept statement holds the names live after it and those the
    swept statement reads or writes. -/
theorem mem_dropDeadDefsStmt_live (D : Defined) (live : Std.HashSet String)
    (added : List String) (stmt : Statement) (n : String) :
    n ∈ (dropDeadDefsStmt F D live added stmt).2.1 ↔ n ∈ live ∨
      n ∈ (Stmt.getVars (dropDeadDefsStmt F D live added stmt).1).map (·.name) ∨
      n ∈ (Stmt.modifiedOrDefinedVars (dropDeadDefsStmt F D live added stmt).1 false).map
        (·.name) := by
  match stmt with
  | .cmd c =>
    rw [dropDeadDefsStmt_cmd]
    simp only [insertTracked_mem, List.map_append, List.mem_append]
  | .exit l md =>
    rw [dropDeadDefsStmt_exit]
    simp [Stmt.getVars]
  | .typeDecl tc md =>
    rw [dropDeadDefsStmt_typeDecl]
    simp [Stmt.getVars]
  | .block l ss md =>
    rw [dropDeadDefsStmt_block, mem_dropDeadDefsAux_live D live added ss n]
    simp only [Stmt.getVars, Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars,
      Stmt.modifiedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte]
  | .loop g m invs body md =>
    rw [dropDeadDefsStmt_loop]
    simp only [insertTracked_mem, mem_dropDeadDefsAux_live D live added body n]
    simp only [Stmt.getVars, Block.getVars, Stmt.modifiedOrDefinedVars,
      Block.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars, Bool.false_eq_true,
      ↓reduceIte, List.append_nil, List.map_append, List.mem_append]
    grind
  | .ite c ts es md =>
    rw [dropDeadDefsStmt_ite]
    split
    · obtain ⟨h₁, h₂, hm, -⟩ := dropDeadDefsArms_spec F D live added es ts
      simp only [insertTracked_mem, hm, h₁, h₂, mem_dropDeadDefsAux_live D live [] es n,
        mem_dropDeadDefsAux_live D live [] ts n, Stmt.getVars, Stmt.modifiedOrDefinedVars,
        Block.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars, Bool.false_eq_true,
        ↓reduceIte, List.map_append, List.mem_append]
      grind
    · obtain ⟨h₁, h₂, hm, -⟩ := dropDeadDefsArms_spec F D live added ts es
      simp only [insertTracked_mem, hm, h₁, h₂, mem_dropDeadDefsAux_live D live [] ts n,
        mem_dropDeadDefsAux_live D live [] es n, Stmt.getVars, Stmt.modifiedOrDefinedVars,
        Block.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars, Bool.false_eq_true,
        ↓reduceIte, List.map_append, List.mem_append]
      grind
  termination_by sizeOf stmt

/-- **The live set before a swept list** holds exactly the names live after it and those
    the statements the sweep kept read or write. -/
theorem mem_dropDeadDefsAux_live (D : Defined) (L : Std.HashSet String)
    (added : List String) (ss : List Statement) (n : String) :
    n ∈ (dropDeadDefsAux F D L added ss).2.1 ↔ n ∈ L ∨
      n ∈ (Block.getVars (dropDeadDefsAux F D L added ss).1).map (·.name) ∨
      n ∈ (Block.modifiedOrDefinedVars (dropDeadDefsAux F D L added ss).1 false).map
        (·.name) := by
  match ss with
  | [] => rw [dropDeadDefsAux_nil]; simp [Block.getVars]
  | s :: rest =>
    by_cases hdead : ∃ y, definedBy F D s = some y ∧
        (dropDeadDefsAux F (D.after s) L added rest).2.1.contains y.name = false
    · obtain ⟨y, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse]
      exact mem_dropDeadDefsAux_live (D.after s) L added rest n
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)]
      simp only
      rw [mem_dropDeadDefsStmt_live, mem_dropDeadDefsAux_live (D.after s) L added rest n]
      simp only [Block.getVars, Block.modifiedOrDefinedVars, Block.modifiedVars,
        Block.definedVars, Stmt.modifiedOrDefinedVars, List.map_append, List.mem_append]
      grind
  termination_by sizeOf ss

end

/-- **A branch's arms are swept independently**: whichever order the sweep takes them in,
    each swept arm is that arm swept on its own from the live set after the branch. -/
theorem dropDeadDefsStmt_ite_arms (live : Std.HashSet String) (added : List String)
    (c : ExprOrNondet Expression) (ts es : List Statement) (md : MetaData Expression) :
    (dropDeadDefsStmt F D live added (.ite c ts es md)).1 =
      .ite c (dropDeadDefsAux F D live [] ts).1 (dropDeadDefsAux F D live [] es).1 md := by
  rw [dropDeadDefsStmt_ite]
  split
  · obtain ⟨h₁, h₂, -⟩ := dropDeadDefsArms_spec F D live added es ts
    simp only [h₁, h₂]
  · obtain ⟨h₁, h₂, -⟩ := dropDeadDefsArms_spec F D live added ts es
    simp only [h₁, h₂]

/-- A kept statement leaves, before it, the live set `liveBefore` names. -/
theorem dropDeadDefsAux_cons_keep_live {L : Std.HashSet String} {added : List String}
    {s : Statement} {rest : List Statement}
    (hkeep : ∀ x, definedBy F D s = some x →
      (dropDeadDefsAux F (D.after s) L added rest).2.1.contains x.name = true) :
    SameLive (dropDeadDefsAux F D L added (s :: rest)).2.1
      (liveBefore (dropDeadDefsAux F (D.after s) L added rest).2.1
        (dropDeadDefsStmt F D (dropDeadDefsAux F (D.after s) L added rest).2.1
          (dropDeadDefsAux F (D.after s) L added rest).2.2 s).1) := fun n => by
  rw [dropDeadDefsAux_cons_keep hkeep]
  simp only
  rw [mem_dropDeadDefsStmt_live, mem_liveBefore]

/-- A name live before a swept list is live after it or read or written by a statement
    the sweep kept. -/
theorem live_dropDeadDefsAux (L : Std.HashSet String) (added : List String)
    (ss : List Statement) {x : CoreIdent} (h : Live (dropDeadDefsAux F D L added ss).2.1 x) :
    Live L x ∨ x ∈ Block.getVars (dropDeadDefsAux F D L added ss).1 ∨
      x ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command)
        (dropDeadDefsAux F D L added ss).1 false := by
  rcases (mem_dropDeadDefsAux_live D L added ss x.name).mp (live_iff_mem.mp h) with
    h | h | h
  · exact .inl (live_iff_mem.mpr h)
  · exact .inr (.inl (mem_of_name_mem h))
  · exact .inr (.inr (mem_of_name_mem h))

end Core.Simplify

end
