/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Statement
import Strata.Languages.Core.CallGraph
import Strata.Languages.Core.Core
import Strata.Languages.Core.CoreGen
import Strata.DL.Util.LabelGen

/-! # Utility functions for program transformation in Strata Core -/

namespace Core
namespace Transform

open LabelGen

def oldVarPrefix (id : String) : String := s!"old_{id}"
def tmpVarPrefix (id : String) : String := s!"tmp_{id}"

def createHavoc (ident : Expression.Ident)
  : Statement := Statement.havoc ident

def createHavocs (ident : List Expression.Ident)
  : List Statement := ident.map createHavoc

def createFvar (ident : Expression.Ident)
  : Expression.Expr
  := Lambda.LExpr.fvar ((): ExpressionMetadata) ident none

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

/-- Checks whether a variable `ident` can be found in program `p` -/
def isGlobalVar (p : Program) (ident : Expression.Ident) : Bool :=
  (p.find? .var ident).isSome


/-- Cached results of program analyses that are helpful for program
    transformation. -/
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
  -- During transformation, it is allowed for currentProgram be slightly stale
  -- (has procedures and functions and statements that are not transformed
  -- yet). For example, procedure inlining will always keep currentProgram that
  -- is before inlining.
  -- However, when transformation is finished, currentProgram must contain the
  -- program that is fully updated (or it has to be .none). runProgram enforces
  -- that currentProgram of this CoreTransformState is updated to be the updated
  -- program.
  currentProgram: Option Program
  currentProcedureName: Option String -- TOOD: currentFunctionName, etc?
  cachedAnalyses: CachedAnalyses

@[simp]
def CoreTransformState.emp : CoreTransformState :=
  { genState := .emp, currentProgram := .none,
    currentProcedureName := .none, cachedAnalyses := .emp }

abbrev Err := String

abbrev CoreTransformM := ExceptT Err (StateM CoreTransformState)

/-- A lifter from CoreGenM to (StateM CoreTransformState) -/
def liftCoreGenM {α : Type} (cgm : CoreGenM α) : StateM CoreTransformState α :=
  fun coreTransformState =>
    let res := cgm coreTransformState.genState
    (res.1, {
      genState := res.2,
      currentProgram := coreTransformState.currentProgram,
      currentProcedureName := coreTransformState.currentProcedureName,
      cachedAnalyses := coreTransformState.cachedAnalyses })

instance : MonadLift CoreGenM (StateM CoreTransformState) where
  monadLift := liftCoreGenM

def getIdentTy? (p : Program) (id : Expression.Ident) := p.getVarTy? id

def getIdentTy! (p : Program) (id : Expression.Ident)
  : CoreTransformM (Expression.Ty) := do
  match getIdentTy? p id with
  | none => throw s!"failed to find type for {Std.format id}"
  | some ty => return ty

def getIdentTys! (p : Program) (ids : List Expression.Ident)
  : CoreTransformM (List Expression.Ty) := do
  match ids with
  | [] => return []
  | id :: rest =>
    let ty ← getIdentTy! p id
    return ty :: (← getIdentTys! p rest)

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
returned list has the shape
`((generated_name, ty), original_name)`
-/
def genOldExprIdentsTrip
  (p : Program)
  (ids : List Expression.Ident)
  : CoreTransformM (List ((Expression.Ident × Expression.Ty) × Expression.Ident)) := do
  let gen_idents ← genOldExprIdents ids
  let tys ← getIdentTys! p ids
  return (gen_idents.zip tys).zip ids

/--
Generate an init statement with rhs as expression
-/
def createInit (trip : (Expression.Ident × Expression.Ty) × Expression.Expr)
  : Statement :=
  match trip with
  | ((v', ty), e) => Statement.init v' ty e

def createInits (trips : List ((Expression.Ident × Expression.Ty) × Expression.Expr))
  : List Statement :=
  trips.map createInit

/--
Generate an init statement with rhs as a free variable reference
-/
def createInitVar (trip : (Expression.Ident × Expression.Ty) × Expression.Ident)
  : Statement :=
  match trip with
  | ((v', ty), v) => Statement.init v' ty (Lambda.LExpr.fvar () v none)

def createInitVars (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
  : List Statement :=
  trips.map createInitVar

/-- turns a list of preconditions into assumes with substitution -/
def createAsserts
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    : CoreTransformM (List Statement)
    := conds.mapM (fun (l, check) => do
          let newLabel ← genIdent l (fun s => s!"callElimAssert_{s}")
          return Statement.assert newLabel.toPretty (Lambda.LExpr.substFvars check.expr subst))

/-- turns a list of preconditions into assumes with substitution -/
def createAssumes
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    : CoreTransformM (List Statement)
    :=
    conds.mapM (fun (l, check) => do
      let newLabel ← genIdent l (fun s => s!"callElimAssume_{s}")
      return Statement.assume newLabel.toPretty (Lambda.LExpr.substFvars check.expr subst))

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
      | .goto _lbl _md =>
        return (false, [s]))
    return ⟨changed0 || changed, (sres ++ ss'')⟩
termination_by sizeOf ss
decreasing_by
  all_goals (unfold Imperative.instSizeOfBlock; decreasing_tactic)

/--
Visit all procedures and run f. The returned Bool corresponds to whether the
program has been updated.
NOTE: please use runProgram if possible since CoreTransformState might result
in an inconsistent state. This function is for partial implementation.
-/
private def runProcedures
    (f : Command → CoreTransformM (Option (List Statement)))
    (dcls : List Decl)
    (targetProcList : Option (List String) := .none)
    : CoreTransformM (Bool × List Decl) := do
  match dcls with
  | [] => return (false, [])
  | d :: ds =>
    match d with
    | .proc proc md =>
      if (match targetProcList with
         | .none => true
         | .some p => proc.header.name.1 ∈ p) then
        modify (fun σ => { σ with
          currentProcedureName := .some proc.header.name.1
        })
        let (changed, new_body) ← runStmtsRec f proc.body
        let (changed', new_procs) ← runProcedures (targetProcList := targetProcList) f ds
        return (changed || changed',
          Decl.proc {
            proc with body := new_body
          } md :: new_procs)
      else
        let (changed', new_procs) ← runProcedures (targetProcList := targetProcList) f ds
        return (changed', d :: new_procs)
    | _ =>
      let (changed', new_procs) ← runProcedures (targetProcList := targetProcList) f ds
      return (changed', d :: new_procs)


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
  let (changed, newDecls) ← runProcedures
    (targetProcList := targetProcList) f p.decls
  let newProg := { decls := newDecls }
  modify (fun σ => { σ with
    currentProgram := .some newProg,
    currentProcedureName := .none
  })
  return (changed, newProg)


@[simp]
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
