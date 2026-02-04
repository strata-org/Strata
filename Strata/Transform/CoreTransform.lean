/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Statement
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

abbrev Err := String

abbrev CoreTransformM := ExceptT Err CoreGenM

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


/- Generic runner functions -/

-- Only visit top-level statements and run f
def runStmts (f : Command → Program → CoreTransformM (List Statement))
    (ss : List Statement) (inputProg : Program)
    : CoreTransformM (List Statement) := do
  match ss with
  | [] => return []
  | s :: ss =>
    let s' := match s with
      | .cmd c => f c inputProg
      | s => return [s]
    let ss' := (runStmts f ss inputProg)
    return (← s') ++ (← ss')

-- Recursively visit all blocks and run f
def runStmtsRec (f : Command → Program → CoreTransformM (List Statement))
    (ss : List Statement) (inputProg : Program)
    : CoreTransformM (List Statement) := do
  match ss with
  | [] => return []
  | s :: ss' =>
    let ss'' ← (runStmtsRec f ss' inputProg)
    let sres ← (match s with
      | .cmd c => do
        let res ← f c inputProg
        return res
      | .block lbl b md => do
        let b' ← runStmtsRec f b inputProg
        return [.block lbl b' md]
      | .ite c thenb elseb md => do
        let thenb' ← runStmtsRec f thenb inputProg
        let elseb' ← runStmtsRec f elseb inputProg
        return [.ite c thenb' elseb' md]
      | .loop guard measure invariant body md => do
        let body' ← runStmtsRec f body inputProg
        return [.loop guard measure invariant body' md]
      | .goto _lbl _md =>
        return [s])
    return (sres ++ ss'')
termination_by sizeOf ss
decreasing_by
  all_goals (unfold Imperative.instSizeOfBlock; decreasing_tactic)

def runProcedures (f : Command → Program → CoreTransformM (List Statement))
    (dcls : List Decl) (inputProg : Program)
    : CoreTransformM (List Decl) := do
  match dcls with
  | [] => return []
  | d :: ds =>
    match d with
    | .proc p md =>
      return Decl.proc {
          p with body := ← (runStmtsRec f p.body inputProg)
        } md :: (← (runProcedures f ds inputProg))
    | _ => return d :: (← (runProcedures f ds inputProg))

def runProgram (f : Command → Program → CoreTransformM (List Statement))
    (p : Program) : CoreTransformM Program := do
  let newDecls ← runProcedures f p.decls p
  return { decls := newDecls }


@[simp]
def runWith {α : Type} (p : α) (f : α → CoreTransformM β)
    (s : CoreGenState):
  Except Err β × CoreGenState :=
  (StateT.run (f p) s)

@[simp]
def run {α : Type} (p : α) (f : α → CoreTransformM β)
      (s : CoreGenState := .emp):
  Except Err β :=
  (runWith p f s).fst

end Transform
end Core
