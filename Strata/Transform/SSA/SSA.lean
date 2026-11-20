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
the obligation program, or a literal or a function value over names of the obligation program.

* `init x := e` / `set x := e`: `e` is folded (`foldE`: an `ite` whose condition folds to a
  Boolean literal is its branch, an `ite` whose branches fold to the same variable or literal is
  that branch, and an operator application whose arguments are literals is evaluated by
  `WPOps.evalOp?`); a variable annotated with the declared type of `x` is recorded
  without output (a copy); a literal, or a function value (`WPOps.lam?`) of at most `lamBudget`
  nodes that the language accepts (`WPOps.recordableLam?`: in Core, one whose abstractions read
  their bound variable at most once or whose body holds no abstraction), is recorded
  (`recorded`), for folding and for substitution into later definitions and assumptions, and
  defined by a fresh `init`, the name obligations read; any other value, a variable without that
  annotation and another function value included, is defined by a fresh `init`, so its
  applications stay applications of that name.  A recorded function value is written in place of
  a name only where the language lets the expression copy it (`WPOps.substLam?`, `substVal`: in
  Core, when it reads each bound variable at most once, or when every occurrence of the name is
  applied to a literal, an operator or a variable whose value is no function value); elsewhere
  the expression reads the name defined for the value.
* `assume a`: dropped when `a` folds to `true` and its label is not one the language keeps
  (`WPOps.keepsTrueAssume`).
* `assert`/`cover`: the obligation on the current names, unfolded (its condition is the guarded
  condition under a substitution of variables for variables, `oblSubS`), or the literal whose
  verdict needs no solver model (`true` for an assertion, which passes; `false` for a cover,
  which is refuted) when a free variable of the condition has a literal value and the condition
  evaluates to that literal under the current values (`oblCond`).  For the other literal the
  condition stays unfolded, so that the solver can give the counterexample or the witness.  The
  output has an `init` only where the input has an `init` or a `set`, so only obligations follow
  an `assert` when only obligations follow it in the input.
* `ite * T E` (the last statement of its list): the arms are translated from the same mapping
  (an undo log, `trail`, restores it after `T`), and an empty arm is dropped, the other one
  inline.  An arm whose assumptions fold to `false` is kept: its obligations are reported, on
  a path that assumes `false`, as symbolic evaluation reports the obligations of a branch whose
  condition is `false`.

The traversal records the value of every name at its `init` (`defs`) and, per obligation of the
input in input order, its record entry (its label and the substitution of its free variables)
or its absence (`obls`).

The phase's input is the guarded program, the types of its free variables, the names of the
enclosing program and the operator data `oe` operator applications are evaluated under
(`ssaEntry`); the entry renaming, the avoided names and the initial state are computed from it
alone.

Key definitions: `ssaEntry`, `ssaEntryRen`, `ssaBody`, `foldE`, `recorded`, `SVal`, `SSt`,
`SOut`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasSubstFvar P] [HasIdent P] [LawfulHasIdent P] [Hashable P.Ident] [HasFvars P]
  [WPOps P]


/-- The current value of a name of the guarded program: a variable of the obligation program
    (with its type annotation), or a value expression, a literal or a function value whose free
    variables are names of the obligation program (with its type and the name of the obligation
    program defined for it, which obligations read). -/
inductive SVal (P : PureExpr) where
  | name (y : P.Ident) (ty : Option P.Ty)
  | lit (e : P.Expr) (ty : P.Ty) (mat : Option P.Ident)

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
  | .lit e _ _ => e

/-- The type of a value, when known. -/
@[expose] def SVal.ty? : SVal P → Option P.Ty
  | .name _ ty => ty
  | .lit _ ty _ => some ty

/-- Is the current value of `z` no function value (a variable, a literal, or none)? -/
@[expose] def atomVal (ρ : Std.HashMap P.Ident (SVal P)) (z : P.Ident) : Bool :=
  match ρ[z]? with
  | some (.lit v _ _) => !WPOps.lam? v
  | _ => true

/-- The expression written in place of the name `x` of `e` whose current value is `o`: the value's
    expression (`SVal.expr`), except for a function value the language does not let `e` copy
    where `e` reads `x` (`WPOps.substLam?`), for which it is the name defined for the value. -/
@[expose] def substVal (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) (x : P.Ident) :
    SVal P → P.Expr
  | .lit v ty (some y) =>
    if WPOps.lam? v && !WPOps.substLam? v x (atomVal ρ) e then HasFvar.mkVar y (some ty) else v
  | o => o.expr

/-- `e` with every name replaced by its current value, a function value as `substVal` writes it. -/
@[expose] def renM (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) : P.Expr :=
  WPOps.substFn e fun x => ρ[x]?.map (substVal ρ e x)

/-- The variable an obligation reads for a name: its current variable when renamed, the name
    defined for its literal when literal-valued; `none` for an unrenamed name. -/
@[expose] def oblVar (ρ : Std.HashMap P.Ident (SVal P)) (x : P.Ident) :
    Option (P.Ident × Option P.Ty) :=
  match ρ[x]? with
  | some (.name y ty) => if y == x then none else some (y, ty)
  | some (.lit _ ty (some y)) => some (y, some ty)
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
  | _, _ => WPOps.sameLit a b

/-- `e` with every name replaced by its current value, evaluated by `WPOps.evalOp?` under the
    operator data `oe` when it is an operator application on literals. -/
@[expose] def evalM (oe : WPOps.OpEnv P) (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) :
    P.Expr :=
  let r := renM ρ e
  (WPOps.evalOp? oe r).getD r

/-- Is the current value of `x` a literal? -/
@[expose] def litValued (ρ : Std.HashMap P.Ident (SVal P)) (x : P.Ident) : Bool :=
  match ρ[x]? with
  | some (.lit _ _ _) => true
  | _ => false

/-- The condition the traversal emits for an obligation on `e` whose verdict needs no solver
    model when its condition is the literal `b` (`true` for an assertion, which passes; `false`
    for a cover, which is refuted): that literal when a free variable of `e` has a literal value
    and `e` evaluates to `b` under the current values (`evalM`), otherwise `e` on the variables
    obligations read (`renM'`), so that the solver can give a counterexample or a witness. -/
@[expose] def oblCond (oe : WPOps.OpEnv P) (b : Bool) (ρ : Std.HashMap P.Ident (SVal P))
    (e : P.Expr) : P.Expr :=
  let v := evalM oe ρ e
  if (exprFV e).any (litValued ρ) && WPOps.boolLit? v == some b then v else renM' ρ e

/-- `e` with every name replaced by its current value, folding the conditionals whose condition
    folds to a Boolean literal and those whose branches fold to the same variable or literal,
    and evaluating the operator applications on literals the other parts become (`evalM`) under
    the operator data `oe`. -/
@[expose] def foldE (oe : WPOps.OpEnv P) (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) :
    P.Expr :=
  match _hv : WPOps.iteView? e with
  | some (c, t, f) =>
    let c' := foldE oe ρ c
    match WPOps.boolLit? c' with
    | some true => foldE oe ρ t
    | some false => foldE oe ρ f
    | none =>
      let t' := foldE oe ρ t
      let f' := foldE oe ρ f
      if sameValue t' f' then t' else WPOps.ite c' t' f'
  | none => evalM oe ρ e
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

/-- The largest function value, in nodes (`WPOps.size`), that the traversal records. -/
@[expose] def lamBudget : Nat := 64

/-- Does the traversal record the folded value `e`, for substitution into later expressions: a
    literal, or a function value of at most `lamBudget` nodes that the language accepts
    (`WPOps.recordableLam?`).  A function value that holds a recorded one (written into it by the
    substitution) is accepted only when none of its abstractions reads its bound variable twice,
    so no beta reduction copies the recorded one: along a chain of definitions the copies of a
    recorded function value do not multiply.  Where a recorded function value is written in an
    expression (`substVal`), no beta reduction of its applications copies an argument larger
    than one node, so nesting its applications does not multiply its copies either. -/
@[expose] def recorded (e : P.Expr) : Bool :=
  WPOps.lit? e || WPOps.lam? e && WPOps.recordableLam? e && decide (WPOps.size e ≤ lamBudget)

/-- The value of an assignment `x := e` (declared type `ty`): a variable is recorded (no
    output), a literal or a function value that `recorded` accepts is recorded and defined by a
    fresh `init` (the name obligations read), any other value is defined by a fresh `init`; the
    output statements.

    A variable `y` is recorded only when `e` folds to `y` annotated with `ty`; otherwise `x` is
    defined by a fresh `init`, as any other value is.  Every later read of a recorded `x` reads
    `y : ty`, so recording an ill-typed copy (`y` annotated with another type, or unannotated)
    would give `y` an annotation its value does not have. -/
@[expose] def assignVal (oe : WPOps.OpEnv P) (x : P.Ident) (ty : P.Ty) (e : P.Expr) :
    SM P (PStmts P × SVal P) := do
  let st ← get
  let e' := foldE oe st.ρ e
  if recorded e' then
    let x' ← sFresh x
    pure ([mkInit x' ty (.det e')], .lit e' ty (some x'))
  else
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

/-- The SSA traversal of a statement list, evaluating operator applications under the operator
    data `oe`; the output is the list's translation. -/
@[expose] def ssaList (oe : WPOps.OpEnv P) : PStmts P → SM P (PStmts P)
  | [] => pure []
  | s :: rest => do
    match s with
    | .cmd (.cmd (.init x ty (.det e) _)) => do
      let (out, v) ← assignVal oe x ty e
      bind x v
      modify fun st => { st with defs := st.defs.insert x v }
      pure (out ++ (← ssaList oe rest))
    | .cmd (.cmd (.init x ty .nondet _)) => do
      let x' ← sFresh x
      let v := SVal.name x' (some ty)
      bind x v
      modify fun st => { st with defs := st.defs.insert x v }
      pure (mkInit x' ty .nondet :: (← ssaList oe rest))
    | .cmd (.cmd (.set x (.det e) _)) => do
      let ty ← curTy x
      let (out, v) ← assignVal oe x ty e
      bind x v
      pure (out ++ (← ssaList oe rest))
    | .cmd (.cmd (.set x .nondet _)) => do
      let ty ← curTy x
      let x' ← sFresh x
      bind x (.name x' (some ty))
      pure (mkInit x' ty .nondet :: (← ssaList oe rest))
    | .cmd (.cmd (.assume l a md)) => do
      let a' := foldE oe (← get).ρ a
      let rest' ← ssaList oe rest
      if WPOps.boolLit? a' == some true && !WPOps.keepsTrueAssume (P := P) l then pure rest'
      else pure (.cmd (.cmd (.assume l a' md)) :: rest')
    | .cmd (.cmd (.assert l e md)) | .cmd (.cmd (.cover l e md)) => do
      let ρ := (← get).ρ
      pushObl (some (.obl l (oblSubS ρ e)))
      let c : PStmt P := match s with
        | .cmd (.cmd (.cover _ _ _)) => .cmd (.cmd (.cover l (oblCond oe false ρ e) md))
        | _ => .cmd (.cmd (.assert l (oblCond oe true ρ e) md))
      pure (c :: (← ssaList oe rest))
    | .ite .nondet tss ess md => do
      if !rest.isEmpty then throw "SSA: `ite *` followed by a statement \
        (the input is not in tree form)"
      let mark := (← get).trailLen
      let t ← ssaList oe tss
      undoTo mark
      let e ← ssaList oe ess
      match t, e with
      | [], e => pure e
      | t, [] => pure t
      | t, e => pure [.ite .nondet t e md]
    | .typeDecl _ _ => ssaList oe rest
    | .ite (.det _) _ _ _ => throw "SSA: deterministic `ite` (the input is not in tree form)"
    | .block _ _ _ => throw "SSA: `block` (the input is not in tree form)"
    | .exit _ _ => throw "SSA: `exit` (the input is not in tree form)"
    | .loop _ _ _ _ _ => throw "SSA: loop (the input is not in tree form)"
    | .cmd (.call p _ _ _) => throw s!"SSA: call to '{p}' (the input is not in tree form)"
  termination_by ss => sizeOf ss

/-- **The SSA phase.**  The obligation program of the guarded program `lay` from the entry
    renaming `ρ0` (every parameter and every `old x` to its entry name, typed by `st.tys`), the
    counter and avoided names of `st`, operator applications evaluated under `oe`. -/
@[expose] def ssaBody (oe : WPOps.OpEnv P) (st : FreshSt P) (ρ0 : Ren P) (lay : PStmts P) :
    Except String (SOut P) := do
  let ρ := ρ0.foldr (fun (x, y) ρ => ρ.insert x (SVal.name y (Tys.get? st.tys x))) {}
  let s0 : SSt P := { next := st.next, avoid := st.avoid, ρ := ρ }
  let (out, s1) ← (ssaList oe lay).run s0
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
    entry renaming of `xs` and `al` (`ssaEntryRen`), then `ssaBody` under the operator data
    `oe`; every fresh name avoids `inputAvoid G tys lay`, the counter starts at `0`.  The result:
    the entry renaming and the output of `ssaBody`. -/
@[expose] def ssaEntry (oe : WPOps.OpEnv P) (G : IdSet P) (tys : Tys P) (xs : List P.Ident)
    (al : List (P.Ident × P.Ident)) (lay : PStmts P) : Except String (Ren P × SOut P) := do
  let (ρ0, n) := ssaEntryRen (inputAvoid G tys lay) xs al 0
  let so ← ssaBody oe ⟨n, inputAvoid G tys lay, tys⟩ ρ0 lay
  pure (ρ0, so)

end -- public section

end WP
end Imperative
