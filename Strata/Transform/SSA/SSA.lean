/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Program

/-! # The SSA phase: guarded program → obligation program (language-generic)

One forward traversal of a *guarded program* (the WP phase's output: `init`, `set`, `assume`,
`assert`, `cover` and `ite *`, every `ite *` the last statement of its list, every name declared
by at most one `init`) producing an *obligation program*: every assignment becomes the definition
of a fresh name, so the output only defines (`init`), assumes and checks, combined by `ite *`.

The traversal maps each name of the guarded program to its current value (`SVal`): a variable of
the obligation program or a Boolean literal.

* `init x := e` / `set x := e`: the condition parts of `e` are folded (`foldE`: an `ite` whose
  condition folds to a literal is its branch, an `ite` whose branches fold to the same variable
  or literal is that branch); a variable annotated with the declared type of `x` is recorded
  without output (a copy); a literal is recorded, for folding, and defined by a fresh `init`,
  the name obligations read; any other value, a variable without that annotation included, is
  defined by a fresh `init`.
* `assume a`: dropped when `a` folds to `true`.
* `assert`/`cover`: the obligation on the current names, unfolded (its condition is the guarded
  condition under a substitution of variables for variables, `oblSubS`).  The output has an
  `init` only where the input has an `init` or a `set`, so only obligations follow an `assert`
  when only obligations follow it in the input.
* `ite * T E` (the last statement of its list): the arms are translated from the same mapping
  (an undo log, `trail`, restores it after `T`), and an empty arm is dropped, the other one
  inline.  An arm whose assumptions fold to `false` is kept: its obligations are reported, on
  a path that assumes `false`, as symbolic evaluation reports the obligations of a branch whose
  condition is `false`.

The traversal records the value of every name at its `init` (`defs`) and, per obligation of the
input in input order, its record entry (its label and the substitution of its free variables)
or its absence (`obls`).

The phase's input is the guarded program, the types of its free variables and the names of the
enclosing program (`ssaEntry`); the entry renaming, the avoided names and the initial state are
computed from it alone.

Key definitions: `ssaEntry`, `ssaEntryRen`, `ssaBody`, `foldE`, `SVal`, `SSt`, `SOut`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasSubstFvar P] [HasIdent P] [LawfulHasIdent P] [Hashable P.Ident] [HasFvars P]
  [WPOps P]


/-- The current value of a name of the guarded program: a variable of the obligation program
    (with its type annotation), or a Boolean literal (with the name of the obligation program
    defined for it, which obligations read). -/
inductive SVal (P : PureExpr) where
  | name (y : P.Ident) (ty : Option P.Ty)
  | lit (b : Bool) (mat : Option P.Ident)
  deriving Inhabited

/-- The SSA state. -/
structure SSt (P : PureExpr) [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBool P] [HasFvar P] [HasSubstFvar P] [HasIdent P] [Hashable P.Ident] [HasFvars P] where
  next : Nat
  avoid : AvoidSet P
  /-- The current value of each name. -/
  ρ : Std.HashMap P.Ident (SVal P) := {}
  /-- The undo log of `ρ` (name, previous value), newest first, and its length. -/
  trail : List (P.Ident × Option (SVal P)) := []
  trailLen : Nat := 0
  /-- The value of each name at its `init` (never undone). -/
  defs : Std.HashMap P.Ident (SVal P) := {}
  /-- Per obligation of the input, its choice-record entry, newest first. -/
  obls : List (Option (LogEntry P)) := []

/-- The result of the SSA phase: the obligation program, per obligation of the input its
    choice-record entry or `none`, the value of each name at its `init`, the final counter. -/
structure SOut (P : PureExpr) where
  out : PStmts P
  obls : List (Option (LogEntry P))
  defs : List (P.Ident × SVal P)
  next : Nat

/-- The SSA monad. -/
abbrev SM (P : PureExpr) [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBool P] [HasFvar P] [HasSubstFvar P] [HasIdent P] [Hashable P.Ident] [HasFvars P] :=
  StateT (SSt P) (Except String)

/-- The expression of a value. -/
@[expose] def SVal.expr : SVal P → P.Expr
  | .name y ty => HasFvar.mkVar y ty
  | .lit b _ => if b then tt else ff

/-- The type of a value, when known. -/
@[expose] def SVal.ty? : SVal P → Option P.Ty
  | .name _ ty => ty
  | .lit _ _ => some HasBool.boolTy

/-- `e` with every name replaced by its current value. -/
@[expose] def renM (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) : P.Expr :=
  WPOps.substFn e fun x => ρ[x]?.map SVal.expr

/-- The variable an obligation reads for a name: its current variable when renamed, the name
    defined for its literal when literal-valued; `none` for an unrenamed name. -/
@[expose] def oblVar (ρ : Std.HashMap P.Ident (SVal P)) (x : P.Ident) :
    Option (P.Ident × Option P.Ty) :=
  match ρ[x]? with
  | some (.name y ty) => if y == x then none else some (y, ty)
  | some (.lit _ (some y)) => some (y, some HasBool.boolTy)
  | _ => none

/-- `e` with every renamed name replaced by its current variable (`oblVar`). -/
@[expose] def renM' (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) : P.Expr :=
  WPOps.substFn e fun x => (oblVar ρ x).map fun (y, ty) => HasFvar.mkVar y ty

/-- The substitution of an obligation's choice-record entry: each renamed free variable with
    its current variable and type annotation. -/
@[expose] def oblSubS (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) :
    List (P.Ident × P.Ident × Option P.Ty) :=
  (exprFV e).filterMap fun x => (oblVar ρ x).map fun (y, ty) => (x, y, ty)

/-- Are the two expressions the same variable or the same literal? -/
@[expose] def sameValue (a b : P.Expr) : Bool :=
  match HasFvar.getFvar a, HasFvar.getFvar b with
  | some x, some y => x == y
  | _, _ =>
    match WPOps.boolLit? a, WPOps.boolLit? b with
    | some x, some y => x == y
    | _, _ => false

/-- `e` with every name replaced by its current value, folding the conditionals whose condition
    folds to a literal and those whose branches fold to the same variable or literal. -/
@[expose] def foldE (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) : P.Expr :=
  match _hv : WPOps.iteView? e with
  | some (c, t, f) =>
    let c' := foldE ρ c
    match WPOps.boolLit? c' with
    | some true => foldE ρ t
    | some false => foldE ρ f
    | none =>
      let t' := foldE ρ t
      let f' := foldE ρ f
      if sameValue t' f' then t' else WPOps.ite c' t' f'
  | none => renM ρ e
  termination_by WPOps.size e
  decreasing_by all_goals have hs := WPOps.iteView?_size _hv; omega

/-- Set the current value of `x`, logging the previous one. -/
@[expose] def bind (x : P.Ident) (v : SVal P) : SM P Unit :=
  modify fun ⟨next, avoid, ρ, trail, trailLen, defs, obls⟩ =>
    let prev := ρ[x]?
    ⟨next, avoid, ρ.insert x v, (x, prev) :: trail, trailLen + 1, defs, obls⟩

/-- Undo the bindings logged after the log had length `mark`. -/
@[expose] def undoTo (mark : Nat) : SM P Unit :=
  modify fun ⟨next, avoid, ρ, trail, trailLen, defs, obls⟩ =>
    let rec go : Nat → List (P.Ident × Option (SVal P)) → Std.HashMap P.Ident (SVal P) →
        List (P.Ident × Option (SVal P)) × Std.HashMap P.Ident (SVal P)
      | 0, tr, ρ => (tr, ρ)
      | _ + 1, [], ρ => ([], ρ)
      | k + 1, (x, old) :: tr, ρ =>
        go k tr (match old with | some v => ρ.insert x v | none => ρ.erase x)
    let (tr, ρ) := go (trailLen - mark) trail ρ
    ⟨next, avoid, ρ, tr, mark, defs, obls⟩

/-- A fresh name with the base of `x`. -/
@[expose] def sFresh (x : P.Ident) : SM P P.Ident := do
  let st ← get
  let (y, n) := freshIn st.avoid (baseOf x) st.next
  set { st with next := n }
  pure y

/-- Record an obligation's choice-record entry (or its absence). -/
@[expose] def pushObl (e : Option (LogEntry P)) : SM P Unit :=
  modify fun st => { st with obls := e :: st.obls }

/-- The value of an assignment `x := e` (declared type `ty`): a variable is recorded (no
    output), a literal is recorded and defined by a fresh Boolean `init` (the name obligations
    read), any other value is defined by a fresh `init`; the output statements.

    A variable `y` is recorded only when `e` folds to `y` annotated with `ty`; otherwise `x` is
    defined by a fresh `init`, as any other value is.  Every later read of a recorded `x` reads
    `y : ty`, so recording an ill-typed copy (`y` annotated with another type, or unannotated)
    would give `y` an annotation its value does not have. -/
@[expose] def assignVal (x : P.Ident) (ty : P.Ty) (e : P.Expr) : SM P (PStmts P × SVal P) := do
  let st ← get
  let e' := foldE st.ρ e
  match WPOps.boolLit? e' with
  | some b =>
    let x' ← sFresh x
    pure ([mkInit x' HasBool.boolTy (.det (if b then tt else ff))], .lit b (some x'))
  | none =>
    match HasFvar.getFvar e' with
    | some y =>
      if (HasFvars.getTypedFvars e').any (fun p => p.1 == y && WPOps.tyBEq p.2 ty) then
        pure ([], .name y (some ty))
      else
        let x' ← sFresh x
        pure ([mkInit x' ty (.det e')], .name x' (some ty))
    | none =>
      let x' ← sFresh x
      pure ([mkInit x' ty (.det e')], .name x' (some ty))

/-- The declared type of the current value of `x`. -/
@[expose] def curTy (x : P.Ident) : SM P P.Ty := do
  let st ← get
  match (st.ρ[x]?.getD (.name x none)).ty? with
  | some ty => pure ty
  | none => throw s!"SSA: assignment to '{WPOps.name x}' of unknown type"

/-- The SSA traversal of a statement list; the output is the list's translation. -/
@[expose] def ssaList : PStmts P → SM P (PStmts P)
  | [] => pure []
  | s :: rest => do
    match s with
    | .cmd (.cmd (.init x ty (.det e) _)) => do
      let (out, v) ← assignVal x ty e
      bind x v
      modify fun st => { st with defs := st.defs.insert x v }
      pure (out ++ (← ssaList rest))
    | .cmd (.cmd (.init x ty .nondet _)) => do
      let x' ← sFresh x
      let v := SVal.name x' (some ty)
      bind x v
      modify fun st => { st with defs := st.defs.insert x v }
      pure (mkInit x' ty .nondet :: (← ssaList rest))
    | .cmd (.cmd (.set x (.det e) _)) => do
      let ty ← curTy x
      let (out, v) ← assignVal x ty e
      bind x v
      pure (out ++ (← ssaList rest))
    | .cmd (.cmd (.set x .nondet _)) => do
      let ty ← curTy x
      let x' ← sFresh x
      bind x (.name x' (some ty))
      pure (mkInit x' ty .nondet :: (← ssaList rest))
    | .cmd (.cmd (.assume l a md)) => do
      let a' := foldE (← get).ρ a
      let rest' ← ssaList rest
      if WPOps.boolLit? a' == some true then pure rest'
      else pure (.cmd (.cmd (.assume l a' md)) :: rest')
    | .cmd (.cmd (.assert l e md)) | .cmd (.cmd (.cover l e md)) => do
      let ρ := (← get).ρ
      pushObl (some (.obl l (oblSubS ρ e)))
      let c : PStmt P := match s with
        | .cmd (.cmd (.cover _ _ _)) => .cmd (.cmd (.cover l (renM' ρ e) md))
        | _ => .cmd (.cmd (.assert l (renM' ρ e) md))
      pure (c :: (← ssaList rest))
    | .ite .nondet tss ess md => do
      if !rest.isEmpty then throw "SSA: `ite *` followed by a statement \
        (the input is not in tree form)"
      let mark := (← get).trailLen
      let t ← ssaList tss
      undoTo mark
      let e ← ssaList ess
      match t, e with
      | [], e => pure e
      | t, [] => pure t
      | t, e => pure [.ite .nondet t e md]
    | .typeDecl _ _ => ssaList rest
    | .ite (.det _) _ _ _ => throw "SSA: deterministic `ite` (the input is not in tree form)"
    | .block _ _ _ => throw "SSA: `block` (the input is not in tree form)"
    | .exit _ _ => throw "SSA: `exit` (the input is not in tree form)"
    | .loop _ _ _ _ _ => throw "SSA: loop (the input is not in tree form)"
    | .cmd (.call p _ _) => throw s!"SSA: call to '{p}' (the input is not in tree form)"
  termination_by ss => sizeOf ss

/-- **The SSA phase.**  The obligation program of the guarded program `lay` from the entry
    renaming `ρ0` (every parameter and every `old x` to its entry name, typed by `st.tys`), the
    counter and avoided names of `st`. -/
@[expose] def ssaBody (st : FreshSt P) (ρ0 : Ren P) (lay : PStmts P) : Except String (SOut P) := do
  let ρ := ρ0.foldr (fun (x, y) ρ => ρ.insert x (SVal.name y (Tys.get? st.tys x))) {}
  let s0 : SSt P := { next := st.next, avoid := st.avoid, ρ := ρ }
  let (out, s1) ← (ssaList lay).run s0
  pure ⟨out, s1.obls.reverse, s1.defs.toList, s1.next⟩

/-- The entry renaming: each name of `xs` to a fresh name with its own name as base (avoiding
    `A`, from the counter `n`), then each `(a, x)` of `al` renames `a` to the entry name of `x`
    (a free variable denoting the entry value of another one); the counter after. -/
@[expose] def ssaEntryRen (A : AvoidSet P) (xs : List P.Ident) (al : List (P.Ident × P.Ident))
    (n : Nat) : Ren P × Nat :=
  let r := xs.foldl (fun (r : Ren P × Nat) x =>
    let f := freshIn A (WPOps.name x) r.2
    (Ren.set r.1 x f.1, f.2)) ([], n)
  (al.foldl (fun (ρ : Ren P) (q : P.Ident × P.Ident) => Ren.set ρ q.1 (Ren.get ρ q.2)) r.1, r.2)

/-- **The SSA phase of a guarded program** `lay` whose free variables have the types `tys`: the
    entry renaming of `xs` and `al` (`ssaEntryRen`), then `ssaBody`; every fresh name avoids
    `inputAvoid G tys lay`, the counter starts at `0`.  The result: the entry renaming and the
    output of `ssaBody`. -/
@[expose] def ssaEntry (G : IdSet P) (tys : Tys P) (xs : List P.Ident)
    (al : List (P.Ident × P.Ident)) (lay : PStmts P) : Except String (Ren P × SOut P) := do
  let (ρ0, n) := ssaEntryRen (inputAvoid G tys lay) xs al 0
  let so ← ssaBody ⟨n, inputAvoid G tys lay, tys⟩ ρ0 lay
  pure (ρ0, so)

end -- public section

end WP
end Imperative
