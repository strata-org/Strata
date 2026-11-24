/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardFwd

/-! # Guard propagation on obligation programs

In an obligation program (the output of the WP pipeline, after `betaReduce`), the obligations of
a merged path read the guards of its branches: a definition `init y := ite(g, a, b)` joins two
branches, a *guarded assumption* `assume ite(g, A, true)` states `A` on the branch of `g`, and an
assumption `assume g` (the reach assumption `wp$reach` among them) or `assume ite(g, false, true)`
states a guard's value as a fact of the path.  `guardProp ss` rewrites the condition of every
`assume`, `assert` and `cover` of `ss` with what is known of the guards at its position; the
definitions, the statements and their order stay as they are, so no statement, and in
particular no labelled marker assumption, is dropped.  Only variables and literals are
substituted, so no term is copied: the definitions keep the terms the conditions share.

An expression is rewritten under a *guard map* `K` (guard name ↦ Boolean):

* *Contextual simplification* (`rwG`): through the `ite` nodes at the root of the expression and
  recursively in their parts, `ite(c, t, f)` has its condition rewritten to `c'`; when `c'` is a
  variable `g`, the arm `t` is rewritten under `K` extended by `g ↦ true` and `f` under `g ↦
  false`.  Both arms are kept: a conditional has a value only when both arms have one.
* At the root of any other subterm, every free variable `y` is substituted, in one
  `WPOps.substFn`, by its *replacement* (`look`): the Boolean literal `K[y]` when `y` is known,
  and otherwise the candidate of guard forwarding (`GuardFwd.cand`: the recorded right-hand side
  of `y`, or the arm of its recorded merge `ite(g, a, b)` that `K[g]` selects) when that
  candidate is a variable or a literal, followed through the replacement of the candidate
  variable, so that a chain of merges whose guards are known resolves to its end.

The *facts* of a position are the guard map of the assumptions met before it on the path: after
`assume e`, whose rewritten condition is `g`, `ite(g, true, false)` or `ite(g, false, true)` with
`g` a variable of type `bool` defined earlier on the path, the facts know `g` as `true`, `true` or
`false`.  Every condition is rewritten under the facts of its position.  Facts, types and
recorded right-hand sides entered inside an arm
of an `ite` are forgotten at its end.

The rewrite keeps the value of a condition wherever the facts of its position hold
(`GuardPropCorrect`).

For Core, `Core.GuardProp.guardPropProgram` runs `guardProp` on every structured procedure body,
and `Core.guardPropPipelinePhase` is the pipeline phase that runs it.

Key definitions: `look`, `rwG`, `factOf`, `PSt`, `walk`, `guardProp`,
`Core.GuardProp.guardPropProgram`, `Core.guardPropPipelinePhase`. -/

namespace Imperative
namespace GuardProp

open WP BigStep GuardFwd

public section

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
  [WPOps P]

/-- The Boolean literal of `b`. -/
@[expose] def boolE (b : Bool) : P.Expr := if b then HasBool.tt else HasBool.ff

/-- The replacement of the variable `y` under the guard map `K` and the scope `sc`, following
    at most `fuel` candidate variables: the literal `K[y]` when `y` is known, otherwise the
    candidate of `y` (`GuardFwd.cand`) when it is a variable or a literal, itself replaced when
    it is a variable with a replacement. -/
@[expose] def look (sc : Scope P) (K : Guards P) : Nat → P.Ident → Option P.Expr
  | fuel, y =>
    match K[y]? with
    | some b => some (boolE b)
    | none =>
      match (cand sc K y).filter atomic with
      | some r =>
        match fuel, HasFvar.getFvar r with
        | n + 1, some z => some ((look sc K n z).getD r)
        | _, _ => some r
      | none => none

/-- **Contextual simplification** of `e` under the guard map `K`: through the conditionals at
    the root, each arm rewritten under the value of its condition when the rewritten condition
    is a variable; at the root of any other subterm, every free variable substituted by its
    replacement (`look`). -/
@[expose] def rwG (sc : Scope P) (fuel : Nat) (K : Guards P) (e : P.Expr) : P.Expr :=
  match _hv : WPOps.iteView? e with
  | some (c, t, f) =>
    let c' := rwG sc fuel K c
    match HasFvar.getFvar c' with
    | some g => WPOps.ite c' (rwG sc fuel (K.insert g true) t) (rwG sc fuel (K.insert g false) f)
    | none => WPOps.ite c' (rwG sc fuel K t) (rwG sc fuel K f)
  | none => WPOps.substFn e (look sc K fuel)
  termination_by WPOps.size e
  decreasing_by all_goals have hs := WPOps.iteView?_size _hv; omega

/-- The fact a condition states about a guard, when it is a variable `g` (`g` holds),
    `ite(g, true, false)` (`g` holds) or `ite(g, false, true)` (`g` does not hold). -/
@[expose] def factOf (e : P.Expr) : Option (P.Ident × Bool) :=
  match HasFvar.getFvar e with
  | some g => some (g, true)
  | none =>
    match WPOps.iteView? e with
    | some (c, t, f) =>
      match HasFvar.getFvar c, WPOps.boolLit? t, WPOps.boolLit? f with
      | some g, some true, some false => some (g, true)
      | some g, some false, some true => some (g, false)
      | _, _, _ => none
    | none => none

/-- The state of the walk: the scope (the names defined earlier on the path, each with its
    recorded right-hand side, if any), the declared types of the names defined earlier on the
    path, and the facts. -/
structure PSt (P : PureExpr) [BEq P.Ident] [Hashable P.Ident] where
  scope : Scope P := {}
  tys : Std.HashMap P.Ident P.Ty := {}
  facts : Guards P := {}

/-- Is `g` *stable* in the scope `sc`: defined earlier on the path or by no `init` of the list
    (`ini`), so that it keeps its value until the end of the scope? -/
@[expose] def stable (ini : Std.HashSet P.Ident) (sc : Scope P) (g : P.Ident) : Bool :=
  sc.contains g || !ini.contains g

/-- Is `g` a Boolean variable defined earlier on the path, stable in its scope? -/
@[expose] def boolVar (ini : Std.HashSet P.Ident) (st : PSt P) (g : P.Ident) : Bool :=
  stable ini st.scope g && (st.tys[g]?.map (WPOps.tyBEq · HasBool.boolTy)).getD false

/-- The facts after an assumption whose rewritten condition is `e`: the fact `e` states, when it
    is about a Boolean variable defined earlier on the path. -/
@[expose] def addFact (ini : Std.HashSet P.Ident) (st : PSt P) (e : P.Expr) : Guards P :=
  match factOf e with
  | some (g, b) => if boolVar ini st g then st.facts.insert g b else st.facts
  | none => st.facts

/-- The rewrite of a condition at a position with the state `st`. -/
@[expose] def rwAt (st : PSt P) (e : P.Expr) : P.Expr :=
  rwG st.scope st.scope.size st.facts e

mutual
/-- The walk over a statement list from the state `st` (`ini`: the names some `init` of the list
    defines): the rewritten list and the state after it. -/
@[expose] def walk (ini : Std.HashSet P.Ident) (st : PSt P) : PStmts P → PStmts P × PSt P
  | [] => ([], st)
  | s :: rest =>
    let (s', st) := walkS ini st s
    let (rest', st) := walk ini st rest
    (s' :: rest', st)
/-- The walk over a statement: the rewritten statement and the state after it.  The arms of an
    `ite` and the body of a block start from `st`, and the state after them is `st`. -/
@[expose] def walkS (ini : Std.HashSet P.Ident) (st : PSt P) : PStmt P → PStmt P × PSt P
  | .cmd (.cmd (.init x ty (.det e) md)) =>
    let v := if (HasFvars.getFvars e).all (stable ini st.scope) then some e else none
    (.cmd (.cmd (.init x ty (.det e) md)),
      { st with scope := st.scope.insert x v, tys := st.tys.insert x ty })
  | .cmd (.cmd (.init x ty .nondet md)) =>
    (.cmd (.cmd (.init x ty .nondet md)),
      { st with scope := st.scope.insert x none, tys := st.tys.insert x ty })
  | .cmd (.cmd (.assume l e md)) =>
    let e' := rwAt st e
    (.cmd (.cmd (.assume l e' md)), { st with facts := addFact ini st e' })
  | .cmd (.cmd (.assert l e md)) => (.cmd (.cmd (.assert l (rwAt st e) md)), st)
  | .cmd (.cmd (.cover l e md)) => (.cmd (.cmd (.cover l (rwAt st e) md)), st)
  | .ite c tss ess md => (.ite c (walk ini st tss).1 (walk ini st ess).1 md, st)
  | .block l ss md => (.block l (walk ini st ss).1 md, st)
  | s => (s, st)
end

/-- **Guard propagation.**  The statement list with the conditions of its assumptions,
    assertions and covers rewritten under the facts and the guards known at each position. -/
@[expose] def guardProp (ss : PStmts P) : PStmts P :=
  (walk (Std.HashSet.ofList (Block.assignedVarsH ss)) {} ss).1

end -- public section

end GuardProp
end Imperative

/-! ## The Core phase -/

namespace Core

public section

namespace GuardProp

open Imperative Imperative.GuardProp

/-- **The guard-propagation transform.**  Every procedure of the program with its structured body
    rewritten by `guardProp`, every other declaration unchanged, and whether some procedure body
    changed.  It leaves the transform state as it is. -/
@[expose] def guardPropProgram (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  return p.mapStructuredBodies guardProp

end GuardProp

/-- The guard-propagation pipeline phase: rewrites the conditions of the assumptions, assertions
    and covers of each procedure body under the facts and guards known at each position
    (`Core.GuardProp.guardPropProgram`).  It requires an obligation
    program (`hasObligationForm`, `staticSingleAssignment`, no calls, loops or CFG bodies).  It
    keeps every statement and only rewrites conditions, with free variables, operators and
    annotated variables taken from the input, so it keeps the facts of its input. -/
def guardPropPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "guardProp" GuardProp.guardPropProgram
    (requires := factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment,
                         .hasObligationForm])
    (preserves := Strata.Pipeline.factSetUnion obligationRewritePreserves
      factSet![.noBetaRedexes])

end -- public section

end Core
