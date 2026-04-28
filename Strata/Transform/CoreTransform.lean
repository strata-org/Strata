/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.CallGraph
public import Strata.Languages.Core.CoreGen
public import Strata.DL.Util.LabelGen
public import Strata.Util.Statistics

/-! # Utility functions for program transformation in Strata Core -/

-- sourcerange:file-ok
-- Synthesized expressions from transforms (fresh variables, old-value snapshots)
-- have no source location.

public section

namespace Core
namespace Transform

open LabelGen

def oldVarPrefix (id : String) : String := s!"old_{id}"
def tmpVarPrefix (id : String) : String := s!"tmp_{id}"

def createHavoc (ident : Expression.Ident)
    (md : Imperative.MetaData Expression)
  : Statement := Statement.havoc ident md

@[expose]
def createHavocs (ident : List Expression.Ident) (md : (Imperative.MetaData Expression))
  : List Statement := ident.map (createHavoc · md)

/-- Create a free variable reference from an identifier.
    Synthesized during transforms; no source location available. -/
def createFvar (ident : Expression.Ident)
  : Expression.Expr
  := Lambda.LExpr.fvar Strata.SourceRange.none ident none

@[expose]
def createFvars (ident : List Expression.Ident)
  : List Expression.Expr
  := ident.map createFvar

def genIdent (ident : Expression.Ident) (pf : String → String)
  : CoreGenM Expression.Ident :=
    CoreGenState.gen (pf ident.name)

/--
Generate identifiers in the form of arg_... that can be used to reduce argument expressions to temporary variables.
-/
def genArgExprIdent
  : CoreGenM Expression.Ident :=
    genIdent "arg" tmpVarPrefix

def genArgExprIdents (n:Nat)
  : CoreGenM (List Expression.Ident) :=
  List.mapM (fun _ => genArgExprIdent) (List.replicate n ())

/--
Retrieves a fresh identifier from the counter generator the given identifier "ident" within old(...), or retrieve an existing one from the exprMap
Assumes that ident contains no duplicates
-/
def genOutExprIdent (ident : Expression.Ident)
  : CoreGenM Expression.Ident :=
    genIdent ident tmpVarPrefix

def genOutExprIdents (idents : List Expression.Ident)
  : CoreGenM (List Expression.Ident)
  := List.mapM genOutExprIdent idents

/--
Retrieves a fresh identifier from the counter generator the given identifier "ident" within old(...), or retrieve an existing one from the exprMap
Assumes that ident contains no duplicates
-/
def genOldExprIdent (ident : Expression.Ident)
  : CoreGenM Expression.Ident :=
    genIdent ident oldVarPrefix

def genOldExprIdents (idents : List Expression.Ident)
  : CoreGenM (List Expression.Ident)
  := List.mapM genOldExprIdent idents


/-- Cached results of program analyses that are helpful for program
    transformation.

    Invariant: When `callGraph` is `some cg`, `cg` must reflect the current
    program's procedure call structure. Every procedure in the program must
    have an entry in `cg.callees`, and every call edge must be accounted for.
    Transforms that add, remove, or modify procedures must update the call
    graph accordingly (or set it to `.none` to invalidate it). -/
structure CachedAnalyses where
  callGraph: Option CallGraph := .none

@[simp]
def CachedAnalyses.emp : CachedAnalyses := {}

/-- Define the state of transformation in Strata Core.
  It is the duty of the transformation to update the analysis cache to keep the
  correct information after code transformation, or one can simply drop the
  cached result.
-/
structure CoreTransformState where
  genState: CoreGenState
  -- The program that is being transformed.
  -- The definition of "current" may vary depending on the transformation.
  -- If the transformation is implemented with runProgram or runProgramUntil,
  -- the currentProgram field will store the latest versions of finished
  -- procedures, but the procedure that is being updated might have stale
  -- statements.
  -- When a transformation is finished, currentProgram must contain the
  -- program that is fully updated (or it has to be .none).
  -- Using runProgram/runProgramUntil enforces that currentProgram of this
  -- CoreTransformState is updated to be the updated program.
  currentProgram: Option Program
  currentProcedureName: Option String -- TOOD: currentFunctionName, etc?
  cachedAnalyses: CachedAnalyses
  -- Optional factory for transformations that need to track function
  -- declarations (e.g., PrecondElim). The factory grows as function
  -- declarations are encountered during traversal.
  factory: Option (@Lambda.Factory CoreLParams) := .none
  -- Per-transform statistics counters, keyed by string names.
  statistics: Statistics := {}

@[simp]
def CoreTransformState.emp : CoreTransformState :=
  { genState := .emp, currentProgram := .none,
    currentProcedureName := .none, cachedAnalyses := .emp }

@[expose]
abbrev Err := String

@[expose]
abbrev CoreTransformM := ExceptT Err (StateM CoreTransformState)

/-- A lifter from CoreGenM to (StateM CoreTransformState) -/
def liftCoreGenM {α : Type} (cgm : CoreGenM α) : StateM CoreTransformState α :=
  fun coreTransformState =>
    let res := cgm coreTransformState.genState
    (res.1, {
      genState := res.2,
      currentProgram := coreTransformState.currentProgram,
      currentProcedureName := coreTransformState.currentProcedureName,
      cachedAnalyses := coreTransformState.cachedAnalyses,
      factory := coreTransformState.factory,
      statistics := coreTransformState.statistics })

instance : MonadLift CoreGenM (StateM CoreTransformState) where
  monadLift := liftCoreGenM

/-- Lift an `Except DiagnosticModel` into `CoreTransformM`. -/
def liftDiag {α : Type} (e : Except Strata.DiagnosticModel α) : CoreTransformM α :=
  match e with
  | .ok a => pure a
  | .error dm => throw dm.message

/-- Get the factory from state, throwing if not set. -/
def getFactory : CoreTransformM (@Lambda.Factory CoreLParams) := do
  match (← get).factory with
  | some F => pure F
  | none => throw "factory not set in CoreTransformState"

/-- Update the factory in state. -/
def setFactory (F : @Lambda.Factory CoreLParams) : CoreTransformM Unit :=
  modify fun σ => { σ with factory := some F }

/-- Increment a statistics counter by `n` (default 1), initializing if absent. -/
def incrementStat (key : String) (n : Nat := 1) : CoreTransformM Unit :=
  modify fun σ => { σ with statistics := σ.statistics.increment key n }


/--
returned list has the shape
((generated_name, ty), original_expr)
Only types of the 'inputs' parameter are used
-/
def genArgExprIdentsTrip
  (inputs : @Lambda.LTySignature Visibility)
  (args : List Expression.Expr)
  : CoreTransformM (List ((Expression.Ident × Lambda.LTy) × Expression.Expr))
  := do
  if inputs.length ≠ args.length then throw "input length and args length mismatch"
  else let gen_idents ← genArgExprIdents args.length
       return (gen_idents.zip inputs.unzip.2).zip args

/--
returned list has the shape
`((generated_name, ty), original_name)`
Only types of the 'outputs' parameter are used.
-/
def genOutExprIdentsTrip
  (outputs : @Lambda.LTySignature Visibility)
  (lhs : List Expression.Ident)
  : CoreTransformM (List ((Expression.Ident × Expression.Ty) × Expression.Ident)) := do
  if outputs.length ≠ lhs.length then throw "output length and lhs length mismatch"
  else let gen_idents ← genOutExprIdents lhs
       return (gen_idents.zip outputs.unzip.2).zip lhs

/--
Generate an init statement with rhs as expression
-/
def createInit (trip : (Expression.Ident × Expression.Ty) × Expression.Expr)
    (md:Imperative.MetaData Expression)
  : Statement :=
  match trip with
  | ((v', ty), e) => Statement.init v' ty (.det e) md

def createInits (trips : List ((Expression.Ident × Expression.Ty) × Expression.Expr))
    (md: (Imperative.MetaData Expression))
  : List Statement :=
  trips.map (createInit · md)

/--
Generate an init statement with rhs as a free variable reference.
Synthesized during transforms; no source location available.
-/
def createInitVar (trip : (Expression.Ident × Expression.Ty) × Expression.Ident)
    (md:Imperative.MetaData Expression)
  : Statement :=
  match trip with
  | ((v', ty), v) => Statement.init v' ty (.det (Lambda.LExpr.fvar Strata.SourceRange.none v none)) md

def createInitVars (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
    (md : (Imperative.MetaData Expression))
  : List Statement :=
  trips.map (createInitVar · md)

/-- turns a list of preconditions into asserts with substitution -/
def createAsserts
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : (Imperative.MetaData Expression))
    (labelPrefix : String := "assert_")
    : CoreTransformM (List Statement)
    := conds.mapM (fun (l, check) => do
          let newLabel ← genIdent l (fun s => s!"{labelPrefix}{s}")
          -- Non-lifting: the replacement expressions must be closed (no dangling bvars).
          -- Use the call site as the primary file range, preserving the requires
          -- clause location as a related file range for richer diagnostics.
          let assertMd := check.md.setCallSiteFileRange md
          return Statement.assert newLabel.toPretty (Lambda.LExpr.substFvars check.expr subst) assertMd)

/-- turns a list of preconditions into assumes with substitution -/
def createAssumes
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : (Imperative.MetaData Expression))
    (labelPrefix : String := "assume_")
    : CoreTransformM (List Statement)
    :=
    conds.mapM (fun (l, check) => do
      let newLabel ← genIdent l (fun s => s!"{labelPrefix}{s}")
      -- Non-lifting: the replacement expressions must be closed (no dangling bvars).
      -- Use the call site as the primary file range, preserving the ensures
      -- clause location as a related file range for richer diagnostics.
      let assumeMd := check.md.setCallSiteFileRange md
      return Statement.assume newLabel.toPretty (Lambda.LExpr.substFvars check.expr subst) assumeMd)

/--
Generate the substitution pairs needed for the body of the procedure
-/
def createOldVarsSubst
  (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
  : Map Expression.Ident Expression.Expr :=
    trips.map go where go
    | ((v', _), v) => (v, createFvar v')


/- Generic runner functions. -/

/--
Recursively visit all blocks and run f
NOTE: please use runProgram if possible since CoreTransformState might result
in an inconsistent state. This function is for partial implementation.
-/
private def runStmtsRec (f : Command → CoreTransformM (Option (List Statement)))
    (ss : List Statement)
    : CoreTransformM (Bool × List Statement) := do
  match ss with
  | [] => return (false, [])
  | s :: ss' =>
    let (changed0, ss'') ← (runStmtsRec f ss')
    let (changed, sres) ← (match s with
      | .cmd c => do
        let res ← f c
        match res with
        | .none => return (false, [s])
        | .some s' => return (true, s')
      | .block lbl b md => do
        let (changed, b') ← runStmtsRec f b
        return (changed, [.block lbl b' md])
      | .ite c thenb elseb md => do
        let (changed, thenb') ← runStmtsRec f thenb
        let (changed', elseb') ← runStmtsRec f elseb
        return (changed || changed', [.ite c thenb' elseb' md])
      | .loop guard measure invariant body md => do
        let (changed, body') ← runStmtsRec f body
        return (changed, [.loop guard measure invariant body' md])
      | .funcDecl _ _ =>
        return (false, [s])  -- Function declarations pass through unchanged
      | .typeDecl _ _ =>
        return (false, [s])  -- Type declarations pass through unchanged
      | .exit _lbl _md =>
        return (false, [s]))
    return ⟨changed0 || changed, (sres ++ ss'')⟩

/--
Run f on each command of the program.
Returns (has the program updated?, the updated program).
If targetProcList is .none, apply f to all statements in every procedure.
If targetProcList is .some l, apply f to statements that are in procedures
listed in l only.
-/
def runProgram
    (f : Command → CoreTransformM (Option (List Statement)))
    (p : Program)
    (targetProcList : Option (List String) := .none)
  : CoreTransformM (Bool × Program) := do
  modify (fun σ => { σ with currentProgram := .some p })

  let mut anyChanged := false
  let mut newDecls := p.decls
  for i in [:p.decls.length] do
    match p.decls[i]? with
    | some (.proc proc md) =>
      let isTargetProc := match targetProcList with
         | .none => true
         | .some pl => proc.header.name.1 ∈ pl

      if isTargetProc then
        -- Initialize CoreTransformState
        modify (fun σ => { σ with
          currentProcedureName := .some proc.header.name.1
        })

        let (changed, new_body) ← runStmtsRec f proc.body

        if changed then
          newDecls := newDecls.set i (Decl.proc { proc with body := new_body } md)
          anyChanged := true
          modify (fun σ => { σ with
            currentProgram := .some { decls := newDecls }
          })
    | _ => pure ()

  let newProg : Program := { decls := newDecls }
  modify (fun σ => { σ with
    currentProcedureName := .none
  })
  return (anyChanged, newProg)

/-- Repeatedly apply a command-level transformation until no more changes occur
    or the iteration limit is reached.
    - `maxIters = none`: repeat until a fixed point (no changes).
    - `maxIters = some n`: run up to `n` iterations, stopping early if no change. -/
def runProgramUntil
    (f : Command → CoreTransformM (Option (List Statement)))
    (p : Program)
    (maxIters : Option Nat := none)
    (targetProcList : Option (List String) := .none)
  : CoreTransformM (Bool × Program) := do
  match maxIters with
  | some n =>
    let mut prog := p
    let mut anyChanged := false
    for _ in List.range n do
      let (changed, prog') ← runProgram f prog targetProcList
      prog := prog'
      if changed then anyChanged := true
      if !changed then break
    return (anyChanged, prog)
  | none =>
    let mut prog := p
    let mut anyChanged := false
    repeat
      let (changed, prog') ← runProgram f prog targetProcList
      prog := prog'
      if changed then anyChanged := true
      if !changed then break
    return (anyChanged, prog)

@[expose, simp]
def runWith {α : Type} (p : α) (f : α → CoreTransformM β)
    (s : CoreTransformState):
  Except Err β × CoreTransformState :=
  (StateT.run (f p) s)

@[simp]
def run {α : Type} (p : α) (f : α → CoreTransformM β)
      (s : CoreTransformState := .emp):
  Except Err β :=
  (runWith p f s).fst

end Transform

end Core

end -- public section
