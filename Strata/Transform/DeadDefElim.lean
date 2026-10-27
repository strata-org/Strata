/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.Languages.Core.PipelinePhase
public import Std.Data.HashSet

/-! # Erasing unread definitions of an obligation program

`deadDefElim live ss` removes from the statement list `ss` every `init x : T := e` (or
`init x : T := *`) whose variable no later statement mentions, whatever `T` and `e`.
"Later" is the rest of the statement's list after erasure, and, for a statement of a
branch or block body, also everything after the enclosing statement (`live`, the
identifiers mentioned after the list); for a statement of the `then` branch of an `ite`, it
also includes the `else` branch after erasure.  The rest of a list is processed before its head,
a branch or block body after the rest of its enclosing list, and the `else` branch of an `ite`
before its `then` branch, so one pass reaches the fixpoint: no remaining `init` has an
unmentioned variable.  No other statement is removed or changed.

Erasing an unread `init` never removes a failure (`DeadDefElimCorrect`).

`deadDefElim` recomputes the identifiers of the rest of a list at each statement.
`deadDefElimH` computes the same list (`deadDefElimH_eq` in `DeadDefElimProps`) in one backward
pass that carries the identifiers mentioned later in one hash set.

For Core, `Core.DeadDefElim.deadDefElimProgram` runs `deadDefElimH` on every structured
procedure body, and `Core.deadDefElimPipelinePhase` is the pipeline phase that runs it
(`DeadDefElimCoreCorrect`).

Key definitions: `erasable`, `deadDefElim`, `deadDefElimS`, `deadDefElimH`,
`Core.DeadDefElim.deadDefElimProgram`, `Core.deadDefElimPipelinePhase`. -/

namespace Imperative
namespace DeadDefElim

public section

variable {P : PureExpr} [BEq P.Ident] [HasFvars P]

/-- Is `s` an `init` whose variable is not in `live`? -/
@[expose] def erasable (live : List P.Ident) : Stmt P (CmdExt P) → Bool
  | .cmd (.cmd (.init x _ _ _)) => !live.contains x
  | _ => false

mutual
/-- The statement list without its unread `init`s, `live` being the identifiers
    mentioned after the list. -/
@[expose] def deadDefElim (live : List P.Ident) :
    List (Stmt P (CmdExt P)) → List (Stmt P (CmdExt P))
  | [] => []
  | s :: rest =>
    let rest' := deadDefElim live rest
    if erasable (Block.idents rest' ++ live) s then rest'
    else deadDefElimS (Block.idents rest' ++ live) s :: rest'
/-- The statement with the unread `init`s of its branches or body removed, `live`
    being the identifiers mentioned after it; the `then` branch of an `ite` is processed with
    the identifiers of the processed `else` branch added. -/
@[expose] def deadDefElimS (live : List P.Ident) : Stmt P (CmdExt P) → Stmt P (CmdExt P)
  | .ite c tss ess md =>
    let ess' := deadDefElim live ess
    .ite c (deadDefElim (Block.idents ess' ++ live) tss) ess' md
  | .block l ss md => .block l (deadDefElim live ss) md
  | s => s
end

variable [Hashable P.Ident]

/-- Insert the free variables of an expression. -/
@[expose] def insertFV (h : Std.HashSet P.Ident) (e : P.Expr) : Std.HashSet P.Ident :=
  (HasFvars.getFvars e).foldl (·.insert ·) h

/-- Insert the free variables of a guard (`ExprOrNondet.getVars`). -/
@[expose] def insertGuard (h : Std.HashSet P.Ident) : ExprOrNondet P → Std.HashSet P.Ident
  | .det e => insertFV h e
  | .nondet => h

/-- Insert the identifiers of a call argument: the free variables of an input expression, the
    variable of an input-output or output argument. -/
@[expose] def insertCallArg (h : Std.HashSet P.Ident) : CallArg P → Std.HashSet P.Ident
  | .inArg e => insertFV h e
  | .inoutArg x | .outArg x => h.insert x

/-- Insert the identifiers of a kept command (`Stmt.idents` of the command). -/
@[expose] def insertCmd (h : Std.HashSet P.Ident) : CmdExt P → Std.HashSet P.Ident
  | .cmd (.init x _ (.det e) _) | .cmd (.set x (.det e) _) => insertFV (h.insert x) e
  | .cmd (.init x _ .nondet _) | .cmd (.set x .nondet _) => h.insert x
  | .cmd (.assume _ e _) | .cmd (.assert _ e _) | .cmd (.cover _ e _) => insertFV h e
  | .call _ args _ => args.foldl insertCallArg h

mutual
/-- Insert every identifier of a statement list (`Block.idents`). -/
@[expose] def insertIdents (h : Std.HashSet P.Ident) :
    List (Stmt P (CmdExt P)) → Std.HashSet P.Ident
  | [] => h
  | s :: rest => insertIdents (insertIdent h s) rest
/-- Insert every identifier of a statement (`Stmt.idents`). -/
@[expose] def insertIdent (h : Std.HashSet P.Ident) : Stmt P (CmdExt P) → Std.HashSet P.Ident
  | .cmd c => insertCmd h c
  | .block _ ss _ => insertIdents h ss
  | .ite c tss ess _ => insertIdents (insertIdents (insertGuard h c) tss) ess
  | .loop g m inv body _ =>
    let h := (m.map (insertFV (insertGuard h g))).getD (insertGuard h g)
    insertIdents (inv.foldl (fun h p => insertFV h p.2) h) body
  | .exit _ _ | .typeDecl _ _ => h
end

/-- `deadDefElim` in one backward pass: `h` holds the identifiers mentioned after the list;
    the result is the processed list and `h` with the identifiers of the processed list added.
    The rest of a list is processed before its head, the `else` branch of an `ite` before its
    `then` branch; each kept statement adds its own identifiers once. -/
@[expose] def deadDefElimHL (h : Std.HashSet P.Ident) :
    List (Stmt P (CmdExt P)) → List (Stmt P (CmdExt P)) × Std.HashSet P.Ident
  | [] => ([], h)
  | s :: rest =>
    let (rest', h1) := deadDefElimHL h rest
    match s with
    | .cmd (.cmd (.init x ty e md)) =>
      if h1.contains x then (s :: rest', insertCmd h1 (.cmd (.init x ty e md))) else (rest', h1)
    | .cmd c => (s :: rest', insertCmd h1 c)
    | .ite c tss ess md =>
      let (ess', h2) := deadDefElimHL h1 ess
      let (tss', h3) := deadDefElimHL h2 tss
      (.ite c tss' ess' md :: rest', insertGuard h3 c)
    | .block l ss md =>
      let (ss', h2) := deadDefElimHL h1 ss
      (.block l ss' md :: rest', h2)
    | .loop g m inv body md =>
      (.loop g m inv body md :: rest', insertIdent h1 (.loop g m inv body md))
    | .exit l md => (.exit l md :: rest', h1)
    | .typeDecl tc md => (.typeDecl tc md :: rest', h1)
  termination_by ss => sizeOf ss

/-- `deadDefElim` in one backward pass with one hash set (`deadDefElimHL`). -/
@[expose] def deadDefElimH (live : List P.Ident) (ss : List (Stmt P (CmdExt P))) :
    List (Stmt P (CmdExt P)) :=
  (deadDefElimHL (Std.HashSet.ofList live) ss).1

end -- public section

end DeadDefElim
end Imperative

/-! ## The Core phase -/

namespace Core

public section

namespace DeadDefElim

open Imperative Imperative.DeadDefElim

/-- The declaration with the unread `init`s of its structured procedure body removed, and
    whether that body changed. -/
@[expose] def deadDefElimDecl : Decl → Decl × Bool
  | .proc q md => match q.body with
    | .structured ss =>
      let ss' := deadDefElimH [] ss
      (.proc { q with body := .structured ss' } md, ss' != ss)
    | .cfg _ => (.proc q md, false)
  | d => (d, false)

/-- **The dead-definition transform.**  Every procedure of the program with the unread `init`s
    of its structured body removed, every other declaration unchanged, and whether some
    procedure body changed.  It transforms each body once and leaves the transform state,
    cached analyses included, as it is. -/
@[expose] def deadDefElimProgram (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  let r := p.decls.map deadDefElimDecl
  return (r.any (·.2), { decls := r.map (·.1) })

end DeadDefElim

/-- The dead-definition elimination pipeline phase: removes from each procedure body
    the `init`s whose variable no later statement mentions
    (`Core.DeadDefElim.deadDefElimProgram`).  It requires a program
    - without calls (`noCalls`) and loops (`noLoops`): its correctness is established for
      call-free, loop-free procedure bodies only;
    - whose function preconditions are already checked (`noPrecondsFromFuncs`): an erased
      `init` takes its unchecked preconditions with it;
    - that is type-checked (`typeAnnotated`, which only `typeCheck` establishes): an erased
      `init` takes its type errors with it.
    It only deletes `init`s, so it keeps every fact of its input.  No default pipeline runs
    it; a pipeline names it (`Core.nameablePhases`). -/
def deadDefElimPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "deadDefElim" DeadDefElim.deadDefElimProgram
    (requires := factSet![.noCalls, .noLoops, .noPrecondsFromFuncs, .typeAnnotated])
    (preserves := factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops,
                         .noLoopInvariants, .noLoopMeasures, .staticSingleAssignment,
                         .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards,
                         .hasObligationForm, .noProcedureContracts, .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated])

end -- public section

end Core
