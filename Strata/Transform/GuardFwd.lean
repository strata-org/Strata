/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Lang
public import Strata.Transform.Passive.CoreLang
public import Strata.Transform.SSA.SSA
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.DeadDefElim
public import Std.Data.HashMap
public import Std.Data.HashSet

/-! # Guard forwarding on obligation programs

In an obligation program (the output of the SSA phase), a definition made under a guard reads
`init y := ite(g, a, b)` with `g` a variable.  Where `g` is known to hold, `y` is `a`, and where
it is known not to hold, `y` is `b`.  `guardFwd ss` rewrites the right-hand side of every `init`
and the condition of every `assume` of `ss` with that knowledge, and the condition of every
`assert` and `cover` exactly; every other statement, and the order of the statements, stay as
they are.

The walk goes forward over the statements, carrying the *scope*: the names defined earlier on
the current path, each with the rewritten right-hand side of its `init` when that right-hand side
is recorded.  A right-hand side is recorded only when each of its free variables is defined
earlier on the path or by no `init` of the list, so that it keeps its value until the end of the
scope.  Entries made inside an arm of an `ite` are removed when the arm ends, by an undo log
(`GSt.trail`), so no map is copied.

An expression is rewritten under a *guard map* `K` (guard name ↦ Boolean), empty at the root
of each expression.  The *candidate* of a name `y` under `K` is `a` when the recorded right-hand
side of `y` is `ite(g, a, b)` with `g` a variable and `K[g] = true`, and `b` when `K[g] = false`.

* At a *spine position* (the root, and the arms and the condition of a conditional at a spine
  position): `ite(g, t, f)` with `g` a variable known in `K` is the rewrite of the selected arm;
  `ite(g, t, f)` with `g` a variable unknown in `K` has its arms rewritten under `K` extended by
  `g ↦ true` and `g ↦ false`; any other conditional has its parts rewritten under `K`; a variable
  with a candidate is replaced by it when the candidate is a variable or a Boolean literal
  (`atomic`) or when the variable occurs once in the list.
* At the root of any other subterm, the variables whose candidate is atomic are substituted by it
  in one `WPOps.substFn`, without rewriting below.

A recorded right-hand side that is itself atomic (a variable or a literal) is the candidate of
its name whatever the guard map.  A conditional whose rewritten condition is a Boolean literal is
its selected arm, and one whose rewritten arms are the same variable or the same literal
(`WP.sameValue`) is that arm.

*Guarded-merge folding.*  Under a nonempty guard map, a variable without a candidate is replaced
by the rewrite of its recorded right-hand side (a *descent*) when that rewrite is atomic.  Descents
are made for a variable that occurs once in the list, which is the shape of a chain of merges
`r@k := ite(g@k, a, r@(k-1))`, and, inside a descent started from the condition of a conditional,
for every variable, which reduces the reach flags of the chain (`r@24 := ite(r@20, ite(g@21, false,
true), false)`) to literals under the guards of the chain.  The result of each descent is
memoised per name while the guard map stays the same.  A definition whose variable occurs once at
a spine position inside an arm of another right-hand side is rewritten without descents: the
descents through it are made from the definition that reads it.

Conditions of assertions and covers are rewritten exactly: a variable whose recorded right-hand
side is atomic is replaced by it, and an equality of a variable defined on the path with itself
is `true`.

A candidate is not rewritten again (it was rewritten when it was recorded).  Each node is visited
once by the walk, each recorded name costs O(1) hash operations and one undo entry, and each
definition is descended into from the one definition that reads it.  The guard map is threaded
through the rewrite and restored after each arm, so it is not copied either.

`deadDefElim` must follow this phase: a compound candidate moved to its only use leaves its
definition unread, and only the erasure of unread definitions removes the duplicate.

For Core, `Core.GuardFwd.guardFwdProgram` runs `guardFwd` on every structured procedure body, and
`Core.guardFwdPipelinePhase` is the pipeline phase that runs it.

Key definitions: `GuardOps`, `cand`, `rw`, `rwExact`, `walk`, `guardFwd`,
`Core.GuardFwd.guardFwdProgram`, `Core.guardFwdPipelinePhase`. -/

namespace Imperative
namespace GuardFwd

open WP BigStep

public section

/-- The operation guard forwarding reads beyond those of `WPOps`: the parts of an equality. -/
class GuardOps (P : PureExpr) where
  /-- The two sides of an equality. -/
  eqView? : P.Expr → Option (P.Expr × P.Expr)

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
  [WPOps P] [GuardOps P]

/-- The scope of the walk: the names defined earlier on the current path, each with its recorded
    right-hand side, if any. -/
abbrev Scope (P : PureExpr) [BEq P.Ident] [Hashable P.Ident] :=
  Std.HashMap P.Ident (Option P.Expr)

/-- The guard map of the rewrite: the guards whose value is known at the current position. -/
abbrev Guards (P : PureExpr) [BEq P.Ident] [Hashable P.Ident] := Std.HashMap P.Ident Bool

/-- The state of the walk: the scope, and its undo log (name, previous entry), newest first, with
    its length. -/
structure GSt (P : PureExpr) [BEq P.Ident] [Hashable P.Ident] where
  scope : Scope P := {}
  trail : List (P.Ident × Option (Option P.Expr)) := []
  trailLen : Nat := 0

/-- The memo of the descents under the current guard map: per name, its atomic rewrite, or
    `none` when the rewrite is not atomic. -/
abbrev Memo (P : PureExpr) [BEq P.Ident] [Hashable P.Ident] := Std.HashMap P.Ident (Option P.Expr)

/-- What the walk reads about the whole list: the number of free-variable occurrences of each
    name, the names some `init` (or `set`) of the list defines, and the names occurring at a spine
    position inside an arm of an `init` right-hand side or an `assume` condition. -/
structure Ctx (P : PureExpr) [BEq P.Ident] [Hashable P.Ident] where
  cnt : Std.HashMap P.Ident Nat
  ini : Std.HashSet P.Ident
  inner : Std.HashSet P.Ident

/-- Is the expression a variable or a literal? -/
@[expose] def atomic (r : P.Expr) : Bool :=
  (HasFvar.getFvar r).isSome || (WPOps.boolLit? r).isSome || WPOps.lit? r

/-- The candidate of `y` under `K`: its recorded right-hand side when that is atomic, otherwise
    the selected arm of its recorded `ite(g, a, b)`, `g` a variable known in `K`. -/
@[expose] def cand (sc : Scope P) (K : Guards P) (y : P.Ident) : Option P.Expr :=
  match sc[y]? with
  | some (some d) =>
    if atomic d then some d else
    match WPOps.iteView? d with
    | some (c, a, b) =>
      match HasFvar.getFvar c with
      | some g =>
        match K[g]? with
        | some true => some a
        | some false => some b
        | none => none
      | none => none
    | none => none
  | _ => none

/-- The rewrite of `e` at a spine position under the guard map `K` with the memo `M`, and `K`
    restored with a memo for it.  `fuel` bounds the depth of the descents; `deep` allows a descent
    for every variable, not only for those occurring once; `cond` marks the condition of a
    conditional, whose descents are deep. -/
@[expose] def rw (fuel : Nat) (deep cond : Bool) (sc : Scope P) (cnt : Std.HashMap P.Ident Nat)
    (K : Guards P) (M : Memo P) (e : P.Expr) : P.Expr × Guards P × Memo P :=
  match _hv : WPOps.iteView? e with
  | some (c, t, f) =>
    match (match HasFvar.getFvar c with | some g => K[g]? | none => none) with
    | some true => rw fuel deep false sc cnt K M t
    | some false => rw fuel deep false sc cnt K M f
    | none =>
      let (c', K, M) := rw fuel deep true sc cnt K M c
      match WPOps.boolLit? c' with
      | some true => rw fuel deep false sc cnt K M t
      | some false => rw fuel deep false sc cnt K M f
      | none =>
        match HasFvar.getFvar c with
        | some g =>
          let (t', K, _) := rw fuel deep false sc cnt (K.insert g true) {} t
          let (f', K, _) := rw fuel deep false sc cnt (K.insert g false) {} f
          (if sameValue t' f' then t' else WPOps.ite c' t' f', K.erase g, {})
        | none =>
          let (t', K, M) := rw fuel deep false sc cnt K M t
          let (f', K, M) := rw fuel deep false sc cnt K M f
          (if sameValue t' f' then t' else WPOps.ite c' t' f', K, M)
  | none =>
    match HasFvar.getFvar e with
    | some y =>
      match cand sc K y with
      | some r => (if atomic r || cnt[y]? == some 1 then r else e, K, M)
      | none =>
        if K.isEmpty || !(deep || cnt[y]? == some 1) then (e, K, M) else
        match M[y]? with
        | some (some r) => (r, K, M)
        | some none => (e, K, M)
        | none =>
          match _hf : fuel, sc[y]? with
          | n + 1, some (some d) =>
            let (r, K, M) := rw n (deep || cond) false sc cnt K M d
            if atomic r then (r, K, M.insert y (some r)) else (e, K, M.insert y none)
          | _, _ => (e, K, M)
    | none => (WPOps.substFn e fun y => (cand sc K y).filter atomic, K, M)
  termination_by (fuel, WPOps.size e)
  decreasing_by
    all_goals first
    | (have hs := WPOps.iteView?_size _hv; apply Prod.Lex.right; omega)
    | (subst _hf; apply Prod.Lex.left; simp only [wfParam]; omega)

/-- The rewrite of an expression at the root of a statement (empty guard map and memo), with
    descents of depth at most `fuel`. -/
@[expose] def rwRoot (fuel : Nat) (sc : Scope P) (cnt : Std.HashMap P.Ident Nat) (e : P.Expr) :
    P.Expr :=
  (rw fuel false false sc cnt {} {} e).1

/-- The exact rewrite of an assertion's or a cover's condition: each variable whose recorded
    right-hand side is atomic replaced by it, and an equality of a variable of the scope with
    itself `true`. -/
@[expose] def rwExact (sc : Scope P) (e : P.Expr) : P.Expr :=
  let e' := WPOps.substFn e fun y => match sc[y]? with
    | some (some d) => if atomic d then some d else none
    | _ => none
  match GuardOps.eqView? e' with
  | some (a, b) =>
    match HasFvar.getFvar a, HasFvar.getFvar b with
    | some x, some x' => if x == x' && sc.contains x then HasBool.tt else e'
    | _, _ => e'
  | none => e'

/-- Enter `x` in the scope with the entry `v`, logging its previous entry. -/
@[expose] def GSt.push (st : GSt P) (x : P.Ident) (v : Option P.Expr) : GSt P :=
  match st with
  | ⟨sc, tr, n⟩ =>
    let prev := sc[x]?
    ⟨sc.insert x v, (x, prev) :: tr, n + 1⟩

/-- Undo the `k` newest entries of the log `tr` in the scope `sc`. -/
@[expose] def undoGo : Nat → List (P.Ident × Option (Option P.Expr)) → Scope P →
    List (P.Ident × Option (Option P.Expr)) × Scope P
  | 0, tr, sc => (tr, sc)
  | _ + 1, [], sc => ([], sc)
  | k + 1, (x, old) :: tr, sc =>
    undoGo k tr (match old with | some v => sc.insert x v | none => sc.erase x)

/-- Undo the entries logged after the log had length `mark`. -/
@[expose] def GSt.undoTo (st : GSt P) (mark : Nat) : GSt P :=
  match st with
  | ⟨sc, tr, n⟩ =>
    let r := undoGo (n - mark) tr sc
    ⟨r.2, r.1, mark⟩

/-- Is the rewritten right-hand side `e` recorded: is each of its free variables defined earlier
    on the path or by no `init` of the list? -/
@[expose] def recordable (cx : Ctx P) (sc : Scope P) (e : P.Expr) : Bool :=
  (HasFvars.getFvars e).all fun z => sc.contains z || !cx.ini.contains z

/-- The depth of the descents for the right-hand side of `init x`: none when `x` occurs once, at
    a spine position inside an arm (its descents are made from the definition that reads it); the
    number of names entered on the path otherwise. -/
@[expose] def initFuel (cx : Ctx P) (st : GSt P) (x : P.Ident) : Nat :=
  if cx.inner.contains x && cx.cnt[x]? == some 1 then 0 else st.trailLen

mutual
/-- The walk over a statement list from the state `st`: the rewritten list and the state after
    it. -/
@[expose] def walk (cx : Ctx P) (st : GSt P) : PStmts P → PStmts P × GSt P
  | [] => ([], st)
  | s :: rest =>
    let (s', st) := walkS cx st s
    let (rest', st) := walk cx st rest
    (s' :: rest', st)
/-- The walk over a statement: the rewritten statement and the state after it.  The arms of an
    `ite` and the body of a block start from `st` and their entries are undone at their end. -/
@[expose] def walkS (cx : Ctx P) (st : GSt P) : PStmt P → PStmt P × GSt P
  | .cmd (.cmd (.init x ty (.det e) md)) =>
    let e' := rwRoot (initFuel cx st x) st.scope cx.cnt e
    (.cmd (.cmd (.init x ty (.det e') md)),
      st.push x (if recordable cx st.scope e' then some e' else none))
  | .cmd (.cmd (.init x ty .nondet md)) => (.cmd (.cmd (.init x ty .nondet md)), st.push x none)
  | .cmd (.cmd (.assume l e md)) =>
    (.cmd (.cmd (.assume l (rwRoot st.trailLen st.scope cx.cnt e) md)), st)
  | .cmd (.cmd (.assert l e md)) => (.cmd (.cmd (.assert l (rwExact st.scope e) md)), st)
  | .cmd (.cmd (.cover l e md)) => (.cmd (.cmd (.cover l (rwExact st.scope e) md)), st)
  | .ite c tss ess md =>
    let m := st.trailLen
    let (tss', st) := walk cx st tss
    let (ess', st) := walk cx (st.undoTo m) ess
    (.ite c tss' ess' md, st.undoTo m)
  | .block l ss md =>
    let m := st.trailLen
    let (ss', st) := walk cx st ss
    (.block l ss' md, st.undoTo m)
  | s => (s, st)
end

/-- Count the free-variable occurrences of `e`. -/
@[expose] def countE (cnt : Std.HashMap P.Ident Nat) (e : P.Expr) : Std.HashMap P.Ident Nat :=
  (HasFvars.getFvars e).foldl (fun m x => m.insert x (m.getD x 0 + 1)) cnt

/-- Count the free-variable occurrences of a guard. -/
@[expose] def countG (cnt : Std.HashMap P.Ident Nat) : ExprOrNondet P → Std.HashMap P.Ident Nat
  | .det e => countE cnt e
  | .nondet => cnt

mutual
/-- Count the free-variable occurrences of the expressions of a statement list. -/
@[expose] def countB (cnt : Std.HashMap P.Ident Nat) : PStmts P → Std.HashMap P.Ident Nat
  | [] => cnt
  | s :: rest => countB (countS cnt s) rest
/-- Count the free-variable occurrences of the expressions of a statement. -/
@[expose] def countS (cnt : Std.HashMap P.Ident Nat) : PStmt P → Std.HashMap P.Ident Nat
  | .cmd (.cmd (.init _ _ e _)) | .cmd (.cmd (.set _ e _)) => countG cnt e
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _))
  | .cmd (.cmd (.cover _ e _)) => countE cnt e
  | .cmd (.call _ _ args _) => args.foldl (fun m a => match a with
      | .inArg e => countE m e
      | _ => m) cnt
  | .ite c tss ess _ => countB (countB (countG cnt c) tss) ess
  | .block _ ss _ => countB cnt ss
  | .loop g m inv body _ =>
    let cnt := (m.map (countE (countG cnt g))).getD (countG cnt g)
    countB (inv.foldl (fun c p => countE c p.2) cnt) body
  | .exit _ _ | .typeDecl _ _ => cnt
end

/-- Add the variables at a spine position of `e` inside an arm (`under`: `e` is inside an arm). -/
@[expose] def armVars (acc : Std.HashSet P.Ident) (under : Bool) (e : P.Expr) :
    Std.HashSet P.Ident :=
  match _hv : WPOps.iteView? e with
  | some (c, t, f) => armVars (armVars (armVars acc under c) true t) true f
  | none =>
    match HasFvar.getFvar e with
    | some y => if under then acc.insert y else acc
    | none => acc
  termination_by WPOps.size e
  decreasing_by all_goals have hs := WPOps.iteView?_size _hv; omega

mutual
/-- Add the variables at a spine position inside an arm of the `init` right-hand sides and the
    `assume` conditions of a statement list. -/
@[expose] def innerB (acc : Std.HashSet P.Ident) : PStmts P → Std.HashSet P.Ident
  | [] => acc
  | s :: rest => innerB (innerS acc s) rest
/-- Add the variables at a spine position inside an arm of the `init` right-hand sides and the
    `assume` conditions of a statement. -/
@[expose] def innerS (acc : Std.HashSet P.Ident) : PStmt P → Std.HashSet P.Ident
  | .cmd (.cmd (.init _ _ (.det e) _)) | .cmd (.cmd (.assume _ e _)) => armVars acc false e
  | .ite _ tss ess _ => innerB (innerB acc tss) ess
  | .block _ ss _ => innerB acc ss
  | _ => acc
end

/-- **Guard forwarding.**  The statement list with the `init` right-hand sides and the `assume`
    conditions rewritten under the guards known at each position, and the conditions of the
    assertions and covers rewritten exactly. -/
@[expose] def guardFwd (ss : PStmts P) : PStmts P :=
  (walk ⟨countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss), innerB {} ss⟩ {} ss).1

end -- public section

end GuardFwd
end Imperative

/-! ## The Core phase -/

namespace Core

public section

namespace GuardFwd

open Imperative Imperative.GuardFwd

/-- The parts of a Core equality. -/
@[expose] def eqView? : Expression.Expr → Option (Expression.Expr × Expression.Expr)
  | .eq _ a b => some (a, b)
  | _ => none

/-- The operation of guard forwarding on Core expressions. -/
instance : GuardOps Expression where
  eqView? := eqView?

/-- **The guard-forwarding transform.**  Every procedure of the program with its structured body
    rewritten by `guardFwd`, every other declaration unchanged, and whether some procedure body
    changed.  It leaves the transform state as it is. -/
@[expose] def guardFwdProgram (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  return p.mapStructuredBodies guardFwd

end GuardFwd

/-- The facts every pass of the rewrite loop of `--vcgen wp` keeps, and so the loop: those of an
    obligation program other than `noBetaRedexes`, which the inlining at the loop's
    normalization and the constructor fold can break by turning an applied conditional whose
    arms are functions into an applied arm.  A pass that also keeps `noBetaRedexes` adds it. -/
@[expose] def obligationRewritePreserves : ProgramFactSet :=
  factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops, .noLoopInvariants, .noLoopMeasures,
    .staticSingleAssignment, .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm,
    .noProcedureContracts, .noPolymorphicProcedures, .noPolymorphicFunctions, .typeAnnotated,
    .noInits, .treeForm, .exitsCovered, .armsHaveObligations]

/-- The guard-forwarding pipeline phase: rewrites the `init` right-hand sides and the `assume`
    conditions of each procedure body under the guards known at each position, and the
    conditions of its assertions and covers exactly
    (`Core.GuardFwd.guardFwdProgram`).  It requires an obligation program (`hasObligationForm`,
    `staticSingleAssignment`, no calls, loops or CFG bodies), the output of the SSA phase.
    `deadDefElimPipelinePhase` must follow it: a compound branch moved to its only use leaves
    its definition unread, and only the erasure of unread definitions removes the duplicate.
    It keeps the statements and only rewrites expressions, with free variables, operators and
    annotated variables taken from the input, so it keeps the facts of its input. -/
def guardFwdPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "guardFwd" GuardFwd.guardFwdProgram
    (requires := factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment,
                         .hasObligationForm])
    (preserves := Strata.Pipeline.factSetUnion obligationRewritePreserves
      factSet![.noBetaRedexes])

end -- public section

end Core
