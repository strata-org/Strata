/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Statement
import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.BoogieGen
import Strata.DL.Util.LabelGen

/-! # Utility functions for program transformation in Boogie -/

namespace Boogie
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
  : BoogieGenM Expression.Ident :=
    BoogieGenState.gen (pf ident.name)

/--
Generate identifiers in the form of arg_... that can be used to reduce argument expressions to temporary variables.
-/
def genArgExprIdent
  : BoogieGenM Expression.Ident :=
    genIdent "arg" tmpVarPrefix

def genArgExprIdents (n:Nat)
  : BoogieGenM (List Expression.Ident) :=
  List.mapM (fun _ => genArgExprIdent) (List.replicate n ())

/--
Retrieves a fresh identifier from the counter generator the given identifier "ident" within old(...), or retrieve an existing one from the exprMap
Assumes that ident contains no duplicates
-/
def genOutExprIdent (ident : Expression.Ident)
  : BoogieGenM Expression.Ident :=
    genIdent ident tmpVarPrefix

def genOutExprIdents (idents : List Expression.Ident)
  : BoogieGenM (List Expression.Ident)
  := List.mapM genOutExprIdent idents

/--
Retrieves a fresh identifier from the counter generator the given identifier "ident" within old(...), or retrieve an existing one from the exprMap
Assumes that ident contains no duplicates
-/
def genOldExprIdent (ident : Expression.Ident)
  : BoogieGenM Expression.Ident :=
    genIdent ident oldVarPrefix

def genOldExprIdents (idents : List Expression.Ident)
  : BoogieGenM (List Expression.Ident)
  := List.mapM genOldExprIdent idents

/-- Checks whether a variable `ident` can be found in program `p` -/
def isGlobalVar (p : Program) (ident : Expression.Ident) : Bool :=
  (p.find? .var ident).isSome

abbrev Err := String

abbrev BoogieTransformM := ExceptT Err BoogieGenM

def getIdentTy? (p : Program) (id : Expression.Ident) := p.getVarTy? id

def getIdentTy! (p : Program) (id : Expression.Ident)
  : BoogieTransformM (Expression.Ty) := do
  match getIdentTy? p id with
  | none => throw s!"failed to find type for {Std.format id}"
  | some ty => return ty

def getIdentTys! (p : Program) (ids : List Expression.Ident)
  : BoogieTransformM (List Expression.Ty) := do
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
  : BoogieTransformM (List ((Expression.Ident × Lambda.LTy) × Expression.Expr))
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
  : BoogieTransformM (List ((Expression.Ident × Expression.Ty) × Expression.Ident)) := do
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
  : BoogieTransformM (List ((Expression.Ident × Expression.Ty) × Expression.Ident)) := do
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
    (pres : List Expression.Expr)
    (subst : Map Expression.Ident Expression.Expr)
    : List Statement
    := pres |> List.mapIdx
                (λ i pred ↦
                    Statement.assert s!"assert_{i}" (Lambda.LExpr.substFvars pred subst))

/-- turns a list of preconditions into assumes with substitution -/
def createAssumes
    (posts : List Expression.Expr)
    (subst : Map Expression.Ident Expression.Expr)
    : List Statement
    := posts |> List.mapIdx
                  (λ i pred ↦
                      Statement.assume s!"assume_{i}" (Lambda.LExpr.substFvars pred subst))

/--
Generate the substitution pairs needed for the body of the procedure
-/
def createOldVarsSubst
  (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
  : Map Expression.Ident Expression.Expr :=
    trips.map go where go
    | ((v', _), v) => (v, createFvar v')



/- Generic runner functions -/

def runStmts (f : Statement → Program → BoogieTransformM (List Statement))
    (ss : List Statement) (inputProg : Program)
    : BoogieTransformM (List Statement) := do
  match ss with
  | [] => return []
  | s :: ss =>
    let s' := (f s inputProg)
    let ss' := (runStmts f ss inputProg)
    return (← s') ++ (← ss')

def runProcedures (f : Statement → Program → BoogieTransformM (List Statement))
    (dcls : List Decl) (inputProg : Program)
    : BoogieTransformM (List Decl) := do
  match dcls with
  | [] => return []
  | d :: ds =>
    match d with
    | .proc p md =>
      return Decl.proc { p with body := ← (runStmts f p.body inputProg ) } md ::
        (← (runProcedures f ds inputProg))
    | _ => return d :: (← (runProcedures f ds inputProg))

def runProgram (f : Statement → Program → BoogieTransformM (List Statement))
    (p : Program) : BoogieTransformM Program := do
  let newDecls ← runProcedures f p.decls p
  return { decls := newDecls }


@[simp]
def runWith {α : Type} (p : α) (f : α → BoogieTransformM β)
    (s : BoogieGenState):
  Except Err β × BoogieGenState :=
  (StateT.run (f p) s)

@[simp]
def run {α : Type} (p : α) (f : α → BoogieTransformM β)
      (s : BoogieGenState := .emp):
  Except Err β :=
  (runWith p f s).fst

end Transform
end Boogie
