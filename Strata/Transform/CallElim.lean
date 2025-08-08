/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.Boogie.Statement
import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.OldExpressions
import Strata.Languages.Boogie.ProgramWF
import Strata.DL.Util.ListUtils
import Strata.Languages.Boogie.BoogieGen
import Strata.DL.Util.LabelGen

/-! # Call Elimination Transformation -/

namespace Boogie
namespace CallElim

open LabelGen

def oldVarPrefix (id : String) : String := s!"old_{id}"
def tmpVarPrefix (id : String) : String := s!"tmp_{id}"

def createHavoc (ident : Expression.Ident)
  : Statement := Statement.havoc ident

def createHavocs (ident : List Expression.Ident)
  : List Statement := ident.map createHavoc

def createFvar (ident : Expression.Ident)
  : Expression.Expr
  := Lambda.LExpr.fvar ident none

def createFvars (ident : List Expression.Ident)
  : List Expression.Expr
  := ident.map createFvar

def genIdent (ident : Expression.Ident) (pf : String → String)
  : BoogieGenM Expression.Ident :=
    BoogieGenState.gen (pf ident.2)

/--
Generate identifiers in the form of arg_... that can be used to reduce argument expressions to temporary variables.
-/
def genArgExprIdent (_ : Expression.Expr)
  : BoogieGenM Expression.Ident :=
    genIdent "arg" tmpVarPrefix

def genArgExprIdents (exprs : List Expression.Expr)
  : BoogieGenM (List Expression.Ident)
  := List.mapM genArgExprIdent exprs

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

abbrev CallElimM := ExceptT Err BoogieGenM

def getIdentTy? (p : Program) (id : Expression.Ident) := p.getVarTy? id

def getIdentTy! (p : Program) (id : Expression.Ident)
  : CallElimM (Expression.Ty) := do
  match getIdentTy? p id with
  | none => throw s!"failed to find type for {Std.format id}"
  | some ty => return ty

def getIdentTys! (p : Program) (ids : List Expression.Ident)
  : CallElimM (List Expression.Ty) := do
  match ids with
  | [] => return []
  | id :: rest =>
    let ty ← getIdentTy! p id
    return ty :: (← getIdentTys! p rest)

/--
returned list has the shape
((generated_name, ty), original_expr)
-/
def genArgExprIdentsTrip
  (inputs : @Lambda.LTySignature BoogieIdent)
  (args : List Expression.Expr)
  : CallElimM (List ((Expression.Ident × Lambda.LTy) × Expression.Expr))
  := do
  if inputs.length ≠ args.length then throw "input length and args length mismatch"
  else let gen_idents ← genArgExprIdents args
       return (gen_idents.zip inputs.unzip.2).zip args

/--
returned list has the shape
`((generated_name, ty), original_name)`
-/
def genOutExprIdentsTrip
  (outputs : @Lambda.LTySignature BoogieIdent)
  (lhs : List Expression.Ident)
  : CallElimM (List ((Expression.Ident × Expression.Ty) × Expression.Ident)) := do
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
  : CallElimM (List ((Expression.Ident × Expression.Ty) × Expression.Ident)) := do
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
  | ((v', ty), v) => Statement.init v' ty (Lambda.LExpr.fvar v none)

def createInitVars (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
  : List Statement :=
  trips.map createInitVar

/-- turns a list of preconditions into assumes with substitution -/
def createAsserts
    (pres : List Expression.Expr)
    (subst : Map Expression.Ident Expression.Expr)
    : List Statement
    := pres |> List.map (λ pred ↦ Lambda.LExpr.substFvars pred subst)
           |> List.map
             (λ pred : Expression.Expr ↦
               Statement.assert s!"assert: {Std.format pred}" pred)

/-- turns a list of preconditions into assumes with substitution -/
def createAssumes
    (posts : List Expression.Expr)
    (subst : Map Expression.Ident Expression.Expr)
    : List Statement
    := posts |> List.map (λ pred ↦ Lambda.LExpr.substFvars pred subst)
            |> List.map
              (λ pred : Expression.Expr ↦
                Statement.assume s!"assume: {Std.format pred}" pred)

/--
Generate the substitution pairs needed for the body of the procedure
-/
def createOldVarsSubst
  (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
  : Map Expression.Ident Expression.Expr :=
    trips.map go where go
    | ((v', _), v) => (v, createFvar v')

/--
The main call elimination transformation algorithm on a single statement.
The returned result is a sequence of statements if the
-/
def callElimStmt (st: Statement) (p : Program)
  : CallElimM (List Statement) := do
    match st with
      | .call lhs procName args _ =>

        let some proc := Program.Procedure.find? p procName | throw s!"Procedure {procName} not found in program"

        let postconditions := OldExpressions.normalizeOldExprs $ proc.spec.postconditions.values.map Procedure.Check.expr

        -- extract old variables in all post conditions
        let oldVars := postconditions.flatMap OldExpressions.extractOldExprVars

        let oldVars := List.eraseDups oldVars

        -- filter out non-global variables
        let oldVars := oldVars.filter (isGlobalVar p)

        let genArgTrips := genArgExprIdentsTrip (Lambda.LMonoTySignature.toTrivialLTy proc.header.inputs) args

        let argTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Expr)
            ← genArgTrips

        -- Monadic operation, generate var mapping for each unique oldVars.
        let genOutTrips := genOutExprIdentsTrip (Lambda.LMonoTySignature.toTrivialLTy proc.header.outputs) lhs
        let outTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Ident)
            ← genOutTrips

        -- Monadic operation, generate var mapping for each unique oldVars.
        let genOldTrips := genOldExprIdentsTrip p oldVars
        let oldTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Ident)
            ← genOldTrips

        -- initialize/declare the newly generated variables
        let argInit := createInits argTrips
        let outInit := createInitVars outTrips
        let oldInit := createInitVars oldTrips

        -- construct substitutions of old variables
        let oldSubst := createOldVarsSubst oldTrips

        -- only need to substitute post conditions.
        let postconditions := OldExpressions.substsOldExprs oldSubst postconditions

        -- generate havoc for return variables, modified variables
        let havoc_ret := createHavocs lhs
        let havoc_mod := createHavocs proc.spec.modifies
        let havocs := havoc_ret ++ havoc_mod

        -- construct substitutions for argument and return
        let arg_subst : List (Expression.Ident × Expression.Expr)
                      := (Map.keys proc.header.inputs).zip $ createFvars argTrips.unzip.fst.unzip.fst
        let ret_subst : List (Expression.Ident × Expression.Expr)
                      := (Map.keys proc.header.outputs).zip $ createFvars lhs

        -- construct assumes and asserts in place of pre/post conditions
        -- generate asserts based on pre-conditions, substituting procedure arguments
        let asserts := createAsserts
                        (Procedure.Spec.getCheckExprs
                          proc.spec.preconditions)
                        (arg_subst ++ ret_subst)
        -- generate assumes based on post-conditions, substituting procedure arguments and returns
        let assumes := createAssumes postconditions
                        (arg_subst ++ ret_subst)

        return argInit ++ outInit ++ oldInit ++ asserts ++ havocs ++ assumes
      | _ => return [ st ]

def callElimStmts (ss: List Statement) (prog : Program)
  : CallElimM (List Statement) := do match ss with
    | [] => return []
    | s :: ss =>
      let s' := (callElimStmt s prog)
      let ss' := (callElimStmts ss prog)
      return (← s') ++ (← ss')

def callElimL (dcls : List Decl) (prog : Program)
  : CallElimM (List Decl) :=
  match dcls with
  | [] => return []
  | d :: ds =>
    match d with
    | .proc p =>
      return Decl.proc { p with body := ← (callElimStmts p.body prog ) } :: (← (callElimL ds prog))
    | _       => return d :: (← (callElimL ds prog))

/-- Call Elimination for an entire program by walking through all procedure
bodies -/
def callElim' (p : Program) : CallElimM Program := return { decls := (← (callElimL p.decls p)) }

@[simp]
def runCallElimWith' {α : Type} (p : α) (f : α → CallElimM β) (s : BoogieGenState):
  Except Err β × BoogieGenState :=
  (StateT.run (f p) s)

@[simp]
def runCallElimWith {α : Type} (p : α) (f : α → CallElimM β) (s : BoogieGenState):
  Except Err β :=
  (runCallElimWith' p f s).fst

/-- run call elimination with an empty counter state (e.g. starting from 0) -/
@[simp]
def runCallElim {α : Type} (p : α) (f : α → CallElimM β):
  Except Err β :=
  runCallElimWith p f .emp

end CallElim
end Boogie
