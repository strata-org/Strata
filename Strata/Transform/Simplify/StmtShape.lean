/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify
import all Strata.DL.Lambda.LExprProps
public import Strata.Languages.Core.IdentifiersProps
import all Strata.Transform.Simplify
import all Strata.Transform.Simplify.Expr
import all Strata.Util.ListMap
import Strata.Util.ListMapProps

/-! # Simplify: the shape of the statement traversal

Facts about `simpStmt` and `simpStmts` that do not depend on how expressions are
evaluated: what the traversal returns for each shape of statement, that the write sets
it builds bottom-up name exactly what `Stmt.modifiedOrDefinedVars` and
`Stmt.definedVars` list, and which values the contexts it builds can record.

## Key results

* `simpStmt_cmd`, `simpStmt_block_eq`, `simpStmt_ite_det_eq`, `simpStmt_ite_nondet_eq`,
  `simpStmt_loop`, `simpStmts_nil`, `simpStmts_cons` and the `simpCmd_*` equations:
  the traversal at each shape.
* `simpStmt_writes` and `simpStmts_writes`: the write sets are exact
  (`Writes.Covers`).
* `mem_invalidate`, `mem_record`, `mem_recordAgreed`, `mem_agreedDefs`: what survives
  forgetting a write set and what a join records.
* `simpStmt_values_sub` and `simpStmts_values_sub`: a value recorded after a statement
  under a name the statement does not write was recorded before it.
* `simpStmt_nodupKeys` and `simpStmts_nodupKeys`: the recorded values keep distinct keys
  (`Ctx.NodupKeys`).
-/

public section

namespace Core.Simplify

open Lambda Imperative

/-! ## Write sets of a branch -/

/-- A variable either arm writes is written by the conditional. -/
theorem mem_writes_ite_arm {cond : ExprOrNondet Expression} {ts es : List Statement}
    {md : MetaData Expression} {b : Bool} {z : CoreIdent}
    (h : z ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command)
      (if b then ts else es) false) :
    z ∈ Stmt.modifiedOrDefinedVars (P := Expression) (C := Command)
      (Stmt.ite cond ts es md) false := by
  cases b <;>
    simp only [Block.modifiedOrDefinedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
      Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append] at h ⊢ <;>
    grind

/-- A variable either arm initializes is initialized by the conditional. -/
theorem mem_definedVars_ite_arm {cond : ExprOrNondet Expression} {ts es : List Statement}
    {md : MetaData Expression} {b : Bool} {z : CoreIdent}
    (h : z ∈ Block.definedVars (P := Expression) (C := Command) (if b then ts else es) false) :
    z ∈ Stmt.definedVars (P := Expression) (C := Command) (Stmt.ite cond ts es md) false := by
  cases b <;>
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append] at h ⊢ <;>
    grind

/-- Every variable a statement defines it also writes. -/
theorem mem_writes_of_definedVars {s : Statement} {z : CoreIdent}
    (h : z ∈ Stmt.definedVars (P := Expression) (C := Command) s false) :
    z ∈ Stmt.modifiedOrDefinedVars (P := Expression) (C := Command) s false := by
  simp only [Stmt.modifiedOrDefinedVars, List.mem_append]
  exact .inr h

/-- Simplifying a base command keeps what it modifies and what it defines. -/
theorem simpCmd_writes (ctx : Ctx) (c : Imperative.Cmd Expression) :
    Imperative.Cmd.modifiedVars (P := Expression) (simpCmd ctx c).1 =
        Imperative.Cmd.modifiedVars (P := Expression) c ∧
      Imperative.Cmd.definedVars (P := Expression) (simpCmd ctx c).1 =
        Imperative.Cmd.definedVars (P := Expression) c := by
  cases c with
  | init x ty e md => cases e <;> exact ⟨rfl, rfl⟩
  | set x e md => cases e <;> exact ⟨rfl, rfl⟩
  | assert | assume | cover => exact ⟨rfl, rfl⟩

/-- What `insertNames` adds is the names of the identifiers it is given. -/
theorem mem_insertNames {names : Std.HashSet String} {vs : List CoreIdent} {n : String} :
    n ∈ insertNames names vs ↔ n ∈ names ∨ n ∈ vs.map (·.name) := by
  unfold insertNames
  induction vs generalizing names with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, beq_iff_eq, List.map_cons,
      List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h.symm)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h.symm)
      · exact .inr h

/-! ## Write sets -/

/-- `w` names exactly the variables of `vars` in its `vars` set and exactly those of
    `defined` in its `defined` set. -/
structure Writes.Covers (w : Writes) (vars defined : List CoreIdent) : Prop where
  vars_iff : ∀ n, n ∈ w.vars ↔ n ∈ vars.map (·.name)
  defined_iff : ∀ n, n ∈ w.defined ↔ n ∈ defined.map (·.name)

/-- The empty write set covers nothing. -/
theorem Writes.covers_empty : Writes.Covers {} [] [] :=
  ⟨fun n => by simp, fun n => by simp⟩

/-- Covering depends only on which names the lists hold. -/
theorem Writes.Covers.of_iff {w : Writes} {vars defined vars' defined' : List CoreIdent}
    (h : w.Covers vars defined)
    (hv : ∀ n, n ∈ vars.map (·.name) ↔ n ∈ vars'.map (·.name))
    (hd : ∀ n, n ∈ defined.map (·.name) ↔ n ∈ defined'.map (·.name)) :
    w.Covers vars' defined' :=
  ⟨fun n => (h.vars_iff n).trans (hv n), fun n => (h.defined_iff n).trans (hd n)⟩

/-- Adding a statement's writes to a write set covers them too. -/
theorem Writes.Covers.insertStmt {w : Writes} {vars defined : List CoreIdent}
    (h : w.Covers vars defined) (s : Statement) :
    (w.insertStmt s).Covers
      (Stmt.modifiedOrDefinedVars s false ++ vars) (Stmt.definedVars s false ++ defined) where
  vars_iff n := by
    simp only [Writes.insertStmt, mem_insertNames, h.vars_iff, List.map_append,
      List.mem_append]
    exact Or.comm
  defined_iff n := by
    simp only [Writes.insertStmt, mem_insertNames, h.defined_iff, List.map_append,
      List.mem_append]
    exact Or.comm

/-- A name is in the union of two name sets when it is in either. -/
private theorem mem_union_names {a b : Std.HashSet String} {n : String} :
    n ∈ a ∪ b ↔ n ∈ a ∨ n ∈ b := by
  simp only [Std.HashSet.mem_iff_contains, Std.HashSet.mem_union_iff]

/-- The union of two write sets covers what each covers. -/
theorem Writes.Covers.union {a b : Writes} {va da vb db : List CoreIdent}
    (ha : a.Covers va da) (hb : b.Covers vb db) :
    (a.union b).Covers (va ++ vb) (da ++ db) where
  vars_iff n := by
    simp only [Writes.union, mem_union_names, ha.vars_iff, hb.vars_iff,
      List.map_append, List.mem_append]
  defined_iff n := by
    simp only [Writes.union, mem_union_names, ha.defined_iff, hb.defined_iff,
      List.map_append, List.mem_append]

/-! ## The traversal at each shape

`simpStmt` destructures what its recursive calls return, so its equations are stated
with projections, which is the form a proof can rewrite with. -/

section Equations

variable (ctx : Ctx)

/-- A deterministic `init` simplifies its right-hand side and records it. -/
theorem simpCmd_init_det (x : CoreIdent) (ty : Expression.Ty) (e : Expression.Expr)
    (md : MetaData Expression) :
    simpCmd ctx (.init x ty (.det e) md) =
      (.init x ty (.det (simplifyExpr ctx e)) md, ctx.record x (simplifyExpr ctx e)) := by
  simp only [simpCmd]

/-- A nondeterministic `init` forgets its variable. -/
theorem simpCmd_init_nondet (x : CoreIdent) (ty : Expression.Ty) (md : MetaData Expression) :
    simpCmd ctx (.init x ty .nondet md) = (.init x ty .nondet md, ctx.invalidateVar x) := by
  simp only [simpCmd]

/-- A deterministic assignment simplifies its right-hand side and records it. -/
theorem simpCmd_set_det (x : CoreIdent) (e : Expression.Expr) (md : MetaData Expression) :
    simpCmd ctx (.set x (.det e) md) =
      (.set x (.det (simplifyExpr ctx e)) md, ctx.record x (simplifyExpr ctx e)) := by
  simp only [simpCmd]

/-- A `havoc` forgets its variable. -/
theorem simpCmd_set_nondet (x : CoreIdent) (md : MetaData Expression) :
    simpCmd ctx (.set x .nondet md) = (.set x .nondet md, ctx.invalidateVar x) := by
  simp only [simpCmd]

/-- An `assert` simplifies its condition and records nothing. -/
theorem simpCmd_assert (l : String) (e : Expression.Expr) (md : MetaData Expression) :
    simpCmd ctx (.assert l e md) = (.assert l (simplifyExpr ctx e) md, ctx) := by
  simp only [simpCmd]

/-- An `assume` simplifies its condition and records nothing. -/
theorem simpCmd_assume (l : String) (e : Expression.Expr) (md : MetaData Expression) :
    simpCmd ctx (.assume l e md) = (.assume l (simplifyExpr ctx e) md, ctx) := by
  simp only [simpCmd]

/-- A `cover` simplifies its condition and records nothing. -/
theorem simpCmd_cover (l : String) (e : Expression.Expr) (md : MetaData Expression) :
    simpCmd ctx (.cover l e md) = (.cover l (simplifyExpr ctx e) md, ctx) := by
  simp only [simpCmd]

/-- A base command becomes the command `simpCmd` returns. -/
theorem simpStmt_cmd (c : Imperative.Cmd Expression) :
    simpStmt ctx (.cmd (.cmd c)) =
      ([.cmd (.cmd (simpCmd ctx c).1)], (simpCmd ctx c).2, .insertStmt (.cmd (.cmd c))) := by
  rw [simpStmt]

/-- A procedure call simplifies its input arguments and forgets what it writes. -/
theorem simpStmt_call (pname : String) (args : List (CallArg Expression))
    (md : MetaData Expression) :
    simpStmt ctx (.cmd (.call pname args md)) =
      ([Statement.call pname (args.map fun a => match a with
          | .inArg e => CallArg.inArg (simplifyExpr ctx e)
          | other => other) md],
        forgetAssigned ctx [.cmd (.call pname args md)],
        .insertStmt (.cmd (.call pname args md))) := by
  rw [simpStmt]; rfl

/-- A block simplifies its body; the values known after it are the body's, less those
    the body wrote. -/
theorem simpStmt_block_eq (l : String) (ss : List Statement) (md : MetaData Expression) :
    simpStmt ctx (.block l ss md) =
      ([.block l (simpStmts ctx ss).1 md],
        { ctx with values := (simpStmts ctx ss).2.1.values }.invalidate
          (simpStmts ctx ss).2.2.vars,
        (simpStmts ctx ss).2.2.union) := by
  rw [simpStmt]

/-- A deterministic branch simplifies its guard and both arms, and joins the contexts of
    the arms that can run. -/
theorem simpStmt_ite_det_eq (c : Expression.Expr) (ts es : List Statement)
    (md : MetaData Expression) :
    simpStmt ctx (.ite (.det c) ts es md) =
      ([.ite (.det (simplifyExpr ctx c)) (simpStmts ctx ts).1 (simpStmts ctx es).1 md],
        ctx.join
          (liveArms (.det (simplifyExpr ctx c)) [(simpStmts ctx ts).2.1, (simpStmts ctx es).2.1])
          ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).vars
          ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).defined,
        ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).union) := by
  rw [simpStmt]

/-- A nondeterministic branch simplifies both arms and joins their contexts. -/
theorem simpStmt_ite_nondet_eq (ts es : List Statement) (md : MetaData Expression) :
    simpStmt ctx (.ite .nondet ts es md) =
      ([.ite .nondet (simpStmts ctx ts).1 (simpStmts ctx es).1 md],
        ctx.join (liveArms .nondet [(simpStmts ctx ts).2.1, (simpStmts ctx es).2.1])
          ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).vars
          ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).defined,
        ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).union) := by
  rw [simpStmt]

/-- A loop is simplified knowing nothing about what its body writes, and forgets what
    the body writes. -/
theorem simpStmt_loop (g : ExprOrNondet Expression) (m : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (body : List Statement)
    (md : MetaData Expression) :
    simpStmt ctx (.loop g m invs body md) =
      ([.loop
          (match g with
            | .det g => .det (simplifyExpr (forgetAssigned ctx body) g)
            | .nondet => .nondet)
          (m.map (simplifyExpr (forgetAssigned ctx body)))
          (invs.map fun (l, i) => (l, simplifyExpr (forgetAssigned ctx body) i))
          (simpStmts (forgetAssigned ctx body) body).1 md],
        ctx.invalidate (simpStmts (forgetAssigned ctx body) body).2.2.vars,
        (simpStmts (forgetAssigned ctx body) body).2.2.union) := by
  unfold simpStmt; rfl

/-- An `exit` is left alone. -/
theorem simpStmt_exit (l : String) (md : MetaData Expression) :
    simpStmt ctx (.exit l md) = ([.exit l md], ctx, id) := by
  rw [simpStmt]

/-- A type declaration is left alone. -/
theorem simpStmt_typeDecl (tc : TypeConstructor) (md : MetaData Expression) :
    simpStmt ctx (.typeDecl tc md) = ([Statement.typeDecl tc md], ctx, id) := by
  rw [simpStmt]

/-- The empty list is left alone and writes nothing. -/
theorem simpStmts_nil : simpStmts ctx [] = ([], ctx, {}) := by
  rw [simpStmts]

/-- A list simplifies its head, then its tail in the context the head leaves. -/
theorem simpStmts_cons (s : Statement) (rest : List Statement) :
    simpStmts ctx (s :: rest) =
      ((simpStmt ctx s).1 ++ (simpStmts (simpStmt ctx s).2.1 rest).1,
        (simpStmts (simpStmt ctx s).2.1 rest).2.1,
        (simpStmt ctx s).2.2 (simpStmts (simpStmt ctx s).2.1 rest).2.2) := by
  rw [simpStmts]

end Equations

/-! ## The write sets are exact

`simpStmt` builds what a statement writes from what its nested lists write, rather than
walking the statement again. These say that the result names exactly the variables the
walkers `Stmt.modifiedOrDefinedVars _ false` and `Stmt.definedVars _ false` list. -/

mutual

/-- The function `simpStmt` returns adds exactly what `s` writes. -/
theorem simpStmt_writes (ctx : Ctx) (s : Statement) {w : Writes} {vars defined : List CoreIdent}
    (h : w.Covers vars defined) :
    ((simpStmt ctx s).2.2 w).Covers
      (Stmt.modifiedOrDefinedVars s false ++ vars) (Stmt.definedVars s false ++ defined) := by
  match s with
  | .cmd (.cmd c) => rw [simpStmt_cmd]; exact h.insertStmt _
  | .cmd (.call pname args md) => rw [simpStmt_call]; exact h.insertStmt _
  | .block l ss md =>
    rw [simpStmt_block_eq]
    refine ((simpStmts_writes ctx ss).union h).of_iff (fun n => ?_) (fun n => ?_) <;>
      simp [Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars]
  | .ite (.det c) ts es md =>
    rw [simpStmt_ite_det_eq]
    refine (((simpStmts_writes ctx ts).union (simpStmts_writes ctx es)).union h).of_iff
      (fun n => ?_) (fun n => ?_) <;>
      simp only [Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars, Stmt.modifiedVars,
        Stmt.definedVars, List.map_append, List.mem_append, Bool.false_eq_true,
        ↓reduceIte] <;>
      grind
  | .ite .nondet ts es md =>
    rw [simpStmt_ite_nondet_eq]
    refine (((simpStmts_writes ctx ts).union (simpStmts_writes ctx es)).union h).of_iff
      (fun n => ?_) (fun n => ?_) <;>
      simp only [Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars, Stmt.modifiedVars,
        Stmt.definedVars, List.map_append, List.mem_append, Bool.false_eq_true,
        ↓reduceIte] <;>
      grind
  | .loop g m invs body md =>
    rw [simpStmt_loop]
    refine ((simpStmts_writes _ body).union h).of_iff (fun n => ?_) (fun n => ?_) <;>
      simp [Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars]
  | .exit l md => rw [simpStmt_exit]; exact h.of_iff (by simp) (by simp)
  | .typeDecl tc md => rw [simpStmt_typeDecl]; exact h.of_iff (by simp) (by simp)
  termination_by sizeOf s

/-- What `simpStmts` returns names exactly what the list writes. -/
theorem simpStmts_writes (ctx : Ctx) (ss : List Statement) :
    (simpStmts ctx ss).2.2.Covers
      (Block.modifiedOrDefinedVars ss false) (Block.definedVars ss false) := by
  match ss with
  | [] => rw [simpStmts_nil]; exact Writes.covers_empty
  | s :: rest =>
    rw [simpStmts_cons]
    refine (simpStmt_writes ctx s (simpStmts_writes _ rest)).of_iff (fun n => ?_)
      (fun n => ?_) <;>
      simp only [Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars, Block.modifiedVars,
        Block.definedVars, List.map_append, List.mem_append] <;>
      grind
  termination_by sizeOf ss

end

/-! ## What the contexts record

Forgetting a write set keeps only entries that neither are written nor mention a written
name; recording a value adds one entry; a join adds only definitions every arm that can
run agrees on. -/

/-- What survives `Ctx.invalidateBy written`: entries of the original whose key, and each
    of whose value's variables, `written` does not name. -/
private theorem mem_invalidateBy {ctx : Ctx} {written : String → Bool} {y : CoreIdent}
    {v : Expression.Expr} (h : (y, v) ∈ (ctx.invalidateBy written).values.toList) :
    (y, v) ∈ ctx.values.toList ∧ written y.name = false ∧
      ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, written f.name = false := by
  have h' := List.mem_filter.mp h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
    Bool.not_eq_true] at h'
  exact ⟨h'.1, h'.2.1, h'.2.2⟩

/-- What survives `Ctx.invalidate names`: entries of the original whose key, and each of
    whose value's variables, is not in `names`. -/
theorem mem_invalidate {ctx : Ctx} {names : Std.HashSet String} {y : CoreIdent}
    {v : Expression.Expr} (h : (y, v) ∈ (ctx.invalidate names).values.toList) :
    (y, v) ∈ ctx.values.toList ∧ y.name ∉ names ∧
      ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, f.name ∉ names := by
  have hby : ∀ {written : String → Bool}, (∀ a, written a = true ↔ a ∈ names) →
      (y, v) ∈ (ctx.invalidateBy written).values.toList →
      (y, v) ∈ ctx.values.toList ∧ y.name ∉ names ∧
        ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, f.name ∉ names := by
    intro written hw hm
    obtain ⟨hm, hy, hf⟩ := mem_invalidateBy hm
    exact ⟨hm, fun hn => by simp [(hw _).mpr hn] at hy,
      fun f hfv hn => by have := hf f hfv; rw [(hw _).mpr hn] at this; cases this⟩
  have hcontains : ∀ a, names.contains a = true ↔ a ∈ names := fun a =>
    Std.HashSet.mem_iff_contains.symm
  unfold Ctx.invalidate at h
  split at h
  · rename_i he
    have hnone : ∀ a, a ∉ names := fun a ha => by
      rw [Std.HashSet.isEmpty_eq_false_iff_exists_mem.mpr ⟨a, ha⟩] at he
      exact Bool.false_ne_true he
    exact ⟨h, hnone _, fun f _ => hnone _⟩
  · split at h
    · split at h
      · rename_i n hl
        exact hby (fun a => by
          rw [← Std.HashSet.mem_toList, hl]; simp) h
      · exact hby hcontains h
    · exact hby hcontains h

/-- What survives `Ctx.invalidateVar x`: entries of the original that neither are `x`'s
    nor mention it. -/
theorem mem_invalidateVar {ctx : Ctx} {x y : CoreIdent} {v : Expression.Expr}
    (h : (y, v) ∈ (ctx.invalidateVar x).values.toList) :
    (y, v) ∈ ctx.values.toList ∧ y.name ≠ x.name ∧
      ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, f.name ≠ x.name := by
  obtain ⟨hm, hy, hf⟩ := mem_invalidateBy h
  exact ⟨hm, by simpa using hy, fun f hfv => by simpa using hf f hfv⟩

/-- An entry after recording `v` for `x` is that very entry, or an entry of the original
    that neither is `x`'s nor mentions it. -/
theorem mem_record {ctx : Ctx} {x y : CoreIdent} {v w : Expression.Expr}
    (h : (y, w) ∈ (ctx.record x v).values.toList) :
    (y = x ∧ w = v) ∨ ((y, w) ∈ ctx.values.toList ∧ y.name ≠ x.name ∧
      ∀ f ∈ HasFvars.getFvars (P := Core.Expression) w, f.name ≠ x.name) := by
  unfold Ctx.record at h
  split at h
  · exact .inr (mem_invalidateVar h)
  · rcases Map.mem_insert h with heq | hm
    · simp only [Prod.mk.injEq] at heq
      exact .inl heq
    · exact .inr (mem_invalidateVar hm)

/-- An entry of a context grown by `recordAgreed` is one of the recorded definitions or
    an entry of the base. -/
theorem mem_recordAgreed {base : Ctx} :
    ∀ (agreed : List (CoreIdent × Expression.Expr)) {p : CoreIdent × Expression.Expr},
      p ∈ (recordAgreed base agreed).values.toList →
      p ∈ agreed ∨ p ∈ base.values.toList := by
  intro agreed
  induction agreed generalizing base with
  | nil => intro p hp; exact .inr hp
  | cons q rest ih =>
    intro p hp
    simp only [recordAgreed, List.foldl_cons] at hp
    rcases ih (base := { base with values := base.values.insert q.1 q.2 })
      (by simpa only [recordAgreed] using hp) with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · rcases Map.mem_insert h with heq | h'
      · exact .inl (heq ▸ List.mem_cons_self)
      · exact .inr h'

/-- `Option`'s equality test on expressions is sound. -/
private theorem eq_of_beq_option {a b : Option Expression.Expr} (h : (a == b) = true) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some v => exact Bool.noConfusion h
  | some u => cases b with
    | none => exact Bool.noConfusion h
    | some v =>
      have huv : u = v := (Lambda.LExpr.beq_eq u v).mp h
      rw [huv]

/-- What `agreedDefs` guarantees of each definition it records: the variable is
    assigned and not scoped, every live context records a value for it equal up to
    source location, and the value mentions no scoped name. -/
theorem mem_agreedDefs {live : List Ctx} {assigned scopedNames : Std.HashSet String}
    {x : CoreIdent} {v : Expression.Expr} (h : (x, v) ∈ agreedDefs live assigned scopedNames) :
    x.name ∈ assigned ∧ x.name ∉ scopedNames ∧
      (∀ c ∈ live, ∃ v', (x, v') ∈ c.values.toList ∧ v'.beqIgnoringMetadata v) ∧
      ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, f.name ∉ scopedNames := by
  match live with
  | [] => simp [agreedDefs] at h
  | first :: rest =>
    -- What the agreement test gives, once the candidate is known to be `first`'s.
    have hagreed : (x, v) ∈ first.values.toList →
        (!scopedNames.contains x.name &&
          rest.all (fun (c : Ctx) => match Map.find? c.values x with
            | some v' => v'.beqIgnoringMetadata v | none => false) &&
          !(HasFvars.getFvars (P := Core.Expression) v).any
            (fun f => scopedNames.contains f.name)) = true →
        x.name ∉ scopedNames ∧
          (∀ c ∈ first :: rest, ∃ v', (x, v') ∈ c.values.toList ∧ v'.beqIgnoringMetadata v) ∧
          ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, f.name ∉ scopedNames := by
      intro hfirst hok
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true,
        List.any_eq_false, Bool.not_eq_true] at hok
      obtain ⟨⟨hsc, hall⟩, hfv⟩ := hok
      refine ⟨fun hm => by simp [Std.HashSet.mem_iff_contains.mp hm] at hsc, ?_,
        fun f hf hm => by
          have := hfv f hf; rw [Std.HashSet.mem_iff_contains.mp hm] at this; cases this⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨v, hfirst, Lambda.LExpr.beqIgnoringMetadata_refl v⟩
      · have hc' := hall c hc
        cases hfind' : Map.find? c.values x with
        | none => simp [hfind'] at hc'
        | some v' =>
          refine ⟨v', Map.find?_mem _ _ _ hfind', ?_⟩
          simp only [hfind'] at hc'
          exact hc'
    simp only [agreedDefs] at h
    split at h
    · obtain ⟨n, hn, hsome⟩ := List.mem_filterMap.mp h
      split at hsome
      · rename_i w hfind
        split at hsome
        · rename_i hok
          simp only [Option.some.injEq, Prod.mk.injEq] at hsome
          obtain ⟨rfl, rfl⟩ := hsome
          exact ⟨Std.HashSet.mem_toList.mp hn,
            hagreed (Map.find?_mem _ _ _ hfind) hok⟩
        · cases hsome
      · cases hsome
    · obtain ⟨hfirst, hok⟩ := List.mem_filter.mp h
      rw [Bool.and_eq_true] at hok
      obtain ⟨hassigned, hok⟩ := hok
      exact ⟨Std.HashSet.mem_iff_contains.mpr hassigned, hagreed hfirst hok⟩

/-- An entry after a join is a definition every live context records, under an assigned
    and unscoped name, or an entry of the base none of whose names is assigned. -/
theorem mem_join {base : Ctx} {live : List Ctx} {assigned scopedNames : Std.HashSet String}
    {y : CoreIdent} {v : Expression.Expr}
    (h : (y, v) ∈ (base.join live assigned scopedNames).values.toList) :
    (y.name ∈ assigned ∧ y.name ∉ scopedNames ∧
      (∀ c ∈ live, ∃ v', (y, v') ∈ c.values.toList ∧ v'.beqIgnoringMetadata v) ∧
      ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, f.name ∉ scopedNames) ∨
    ((y, v) ∈ base.values.toList ∧ y.name ∉ assigned ∧
      ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, f.name ∉ assigned) := by
  unfold Ctx.join at h
  split at h
  · rename_i he
    have hnone : ∀ a, a ∉ assigned := fun a ha => by
      rw [Std.HashSet.isEmpty_eq_false_iff_exists_mem.mpr ⟨a, ha⟩] at he
      exact Bool.false_ne_true he
    exact .inr ⟨h, hnone _, fun _ _ => hnone _⟩
  · rcases mem_recordAgreed _ h with hag | hbase
    · exact .inl (mem_agreedDefs hag)
    · exact .inr (mem_invalidate hbase)

/-! ## The traversal records only what a statement writes -/

/-- A value `simpCmd` leaves recorded under a name the command does not write was
    already recorded. -/
theorem simpCmd_values_sub (ctx : Ctx) (c : Imperative.Cmd Expression) {y : CoreIdent}
    {v : Expression.Expr} (hmem : (y, v) ∈ (simpCmd ctx c).2.values.toList)
    (hkey : y.name ∉ (Stmt.modifiedOrDefinedVars (P := Expression) (C := Command)
      (.cmd (.cmd c)) false).map (·.name)) :
    (y, v) ∈ ctx.values.toList := by
  match c with
  | .init x ty (.det e) md | .set x (.det e) md =>
    rcases mem_record hmem with ⟨rfl, -⟩ | ⟨h, -⟩
    · simp [Stmt.modifiedOrDefinedVars, HasVarsImp.modifiedVars, HasVarsImp.definedVars,
        CmdExt.modifiedVars, CmdExt.definedVars, Cmd.modifiedVars, Cmd.definedVars] at hkey
    · exact h
  | .init x ty .nondet md | .set x .nondet md => exact (mem_invalidateVar hmem).1
  | .assert l e md | .assume l e md | .cover l e md => exact hmem

mutual

/-- A value the traversal leaves recorded after `s` under a name `s` does not write was
    already recorded before it. -/
theorem simpStmt_values_sub (ctx : Ctx) (s : Statement) {y : CoreIdent} {v : Expression.Expr}
    (hmem : (y, v) ∈ (simpStmt ctx s).2.1.values.toList)
    (hkey : y.name ∉ (Stmt.modifiedOrDefinedVars (P := Expression) (C := Command) s
      false).map (·.name)) :
    (y, v) ∈ ctx.values.toList := by
  match s with
  | .cmd (.cmd c) =>
    rw [simpStmt_cmd] at hmem
    exact simpCmd_values_sub ctx c hmem hkey
  | .cmd (.call pname args md) =>
    rw [simpStmt_call, forgetAssigned] at hmem
    exact (mem_invalidate hmem).1
  | .block l ss md =>
    rw [simpStmt_block_eq] at hmem
    exact simpStmts_values_sub ctx ss (mem_invalidate hmem).1
      (by simpa [Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars] using hkey)
  | .ite cond ts es md =>
    have hw := (simpStmts_writes ctx ts).union (simpStmts_writes ctx es)
    have hjoin : ∀ {live : List Ctx}, (y, v) ∈ (ctx.join live
        ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).vars
        ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).defined).values.toList →
        (y, v) ∈ ctx.values.toList := by
      intro live hm
      rcases mem_join hm with ⟨hy, -⟩ | ⟨hb, -⟩
      · refine absurd ?_ hkey
        have hmem := (hw.vars_iff _).mp hy
        simp only [Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars, Stmt.modifiedVars,
          Stmt.definedVars, List.map_append, List.mem_append, Bool.false_eq_true,
          ↓reduceIte] at hmem ⊢
        grind
      · exact hb
    rcases cond with c | _
    · rw [simpStmt_ite_det_eq] at hmem; exact hjoin hmem
    · rw [simpStmt_ite_nondet_eq] at hmem; exact hjoin hmem
  | .loop g m invs body md =>
    rw [simpStmt_loop] at hmem
    exact (mem_invalidate hmem).1
  | .exit l md => rw [simpStmt_exit] at hmem; exact hmem
  | .typeDecl tc md => rw [simpStmt_typeDecl] at hmem; exact hmem
  termination_by sizeOf s

/-- A value the traversal leaves recorded after `ss` under a name `ss` does not write was
    already recorded before it. -/
theorem simpStmts_values_sub (ctx : Ctx) (ss : List Statement) {y : CoreIdent}
    {v : Expression.Expr} (hmem : (y, v) ∈ (simpStmts ctx ss).2.1.values.toList)
    (hkey : y.name ∉ (Block.modifiedOrDefinedVars (P := Expression) (C := Command) ss
      false).map (·.name)) :
    (y, v) ∈ ctx.values.toList := by
  match ss with
  | [] => rw [simpStmts_nil] at hmem; exact hmem
  | s :: rest =>
    rw [simpStmts_cons] at hmem
    have hk : ∀ n, n ∈ (Stmt.modifiedOrDefinedVars (P := Expression) (C := Command) s
          false).map (·.name) ∨
        n ∈ (Block.modifiedOrDefinedVars (P := Expression) (C := Command) rest
          false).map (·.name) →
        n ∈ (Block.modifiedOrDefinedVars (P := Expression) (C := Command) (s :: rest)
          false).map (·.name) := by
      intro n hn
      simp only [Stmt.modifiedOrDefinedVars, Block.modifiedOrDefinedVars, Block.modifiedVars,
        Block.definedVars, List.map_append, List.mem_append] at hn ⊢
      grind
    exact simpStmt_values_sub ctx s
      (simpStmts_values_sub _ rest hmem (fun h => hkey (hk _ (.inr h))))
      (fun h => hkey (hk _ (.inl h)))
  termination_by sizeOf ss

end

/-! ## Recorded values have distinct keys

Every operation on a context filters its values or inserts into them, so a context whose
values have distinct keys keeps them distinct through the traversal. -/

/-- The values recorded in `ctx` have distinct keys. -/
@[expose] def Ctx.NodupKeys (ctx : Ctx) : Prop :=
  (ctx.values.toList.map Prod.fst).Nodup

private theorem Ctx.NodupKeys.invalidateBy {ctx : Ctx} (h : ctx.NodupKeys)
    (written : String → Bool) : (ctx.invalidateBy written).NodupKeys := by
  simp only [Ctx.NodupKeys, Ctx.invalidateBy, Map.ofList, Map.toList] at h ⊢
  exact h.sublist (List.filter_sublist.map _)

/-- Forgetting a write set keeps the keys distinct. -/
theorem Ctx.NodupKeys.invalidate {ctx : Ctx} (h : ctx.NodupKeys) (names : Std.HashSet String) :
    (ctx.invalidate names).NodupKeys := by
  unfold Ctx.invalidate
  repeat' split
  all_goals first | exact h | exact h.invalidateBy _

/-- Forgetting a variable keeps the keys distinct. -/
theorem Ctx.NodupKeys.invalidateVar {ctx : Ctx} (h : ctx.NodupKeys) (x : CoreIdent) :
    (ctx.invalidateVar x).NodupKeys :=
  h.invalidateBy _

/-- Recording a value keeps the keys distinct. -/
theorem Ctx.NodupKeys.record {ctx : Ctx} (h : ctx.NodupKeys) (x : CoreIdent)
    (v : Expression.Expr) : (ctx.record x v).NodupKeys := by
  unfold Ctx.record
  split
  · exact h.invalidateVar x
  · exact Map.nodup_keys_insert (h.invalidateVar x)

/-- Recording agreed definitions keeps the keys distinct. -/
theorem Ctx.NodupKeys.recordAgreed {base : Ctx} (h : base.NodupKeys) :
    ∀ agreed : List (CoreIdent × Expression.Expr), (Simplify.recordAgreed base agreed).NodupKeys
  | [] => h
  | (x, v) :: rest =>
    Ctx.NodupKeys.recordAgreed (base := { base with values := base.values.insert x v })
      (Map.nodup_keys_insert h) rest

/-- A join keeps the keys of its base distinct. -/
theorem Ctx.NodupKeys.join {base : Ctx} (h : base.NodupKeys) (live : List Ctx)
    (assigned scopedNames : Std.HashSet String) :
    (base.join live assigned scopedNames).NodupKeys := by
  unfold Ctx.join
  split
  · exact h
  · exact (h.invalidate _).recordAgreed _

/-- Simplifying a base command keeps the keys distinct. -/
theorem simpCmd_nodupKeys {ctx : Ctx} (h : ctx.NodupKeys) (c : Imperative.Cmd Expression) :
    (simpCmd ctx c).2.NodupKeys := by
  match c with
  | .init x ty (.det e) md | .set x (.det e) md => exact h.record _ _
  | .init x ty .nondet md | .set x .nondet md => exact h.invalidateVar x
  | .assert l e md | .assume l e md | .cover l e md => exact h

mutual

/-- Simplifying a statement keeps the keys distinct. -/
theorem simpStmt_nodupKeys {ctx : Ctx} (h : ctx.NodupKeys) (s : Statement) :
    (simpStmt ctx s).2.1.NodupKeys := by
  match s with
  | .cmd (.cmd c) => rw [simpStmt_cmd]; exact simpCmd_nodupKeys h c
  | .cmd (.call pname args md) => rw [simpStmt_call]; exact h.invalidate _
  | .block l ss md =>
    rw [simpStmt_block_eq]
    exact Ctx.NodupKeys.invalidate (ctx := { ctx with values := (simpStmts ctx ss).2.1.values })
      (simpStmts_nodupKeys h ss) _
  | .ite (.det c) ts es md => rw [simpStmt_ite_det_eq]; exact h.join _ _ _
  | .ite .nondet ts es md => rw [simpStmt_ite_nondet_eq]; exact h.join _ _ _
  | .loop g m invs body md => rw [simpStmt_loop]; exact h.invalidate _
  | .exit l md => rw [simpStmt_exit]; exact h
  | .typeDecl tc md => rw [simpStmt_typeDecl]; exact h
  termination_by sizeOf s

/-- Simplifying a statement list keeps the keys distinct. -/
theorem simpStmts_nodupKeys {ctx : Ctx} (h : ctx.NodupKeys) (ss : List Statement) :
    (simpStmts ctx ss).2.1.NodupKeys := by
  match ss with
  | [] => rw [simpStmts_nil]; exact h
  | s :: rest =>
    rw [simpStmts_cons]
    exact simpStmts_nodupKeys (simpStmt_nodupKeys h s) rest
  termination_by sizeOf ss

end

/-! ## The arms a branch can take -/

/-- Under a deterministic guard, a literal `true` or `false` leaves only the arm it
    selects; any other guard leaves both. -/
theorem liveArms_det {α : Type} (c : Expression.Expr) (a b : α) :
    liveArms (.det c) [a, b] =
      (if c.isTrue then [a] else if c.isFalse then [b] else [a, b]) := by
  simp only [liveArms]

/-- Under a nondeterministic guard, every arm is live. -/
theorem liveArms_nondet {α : Type} (arms : List α) :
    liveArms (ExprOrNondet.nondet (P := Expression)) arms = arms := by
  simp only [liveArms]

end Core.Simplify

end
