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
Only types of the 'inputs' parameter are used
-/
def genArgExprIdentsTrip
  (inputs : @Lambda.LTySignature Visibility)
  (args : List Expression.Expr)
  : CallElimM (List ((Expression.Ident × Lambda.LTy) × Expression.Expr))
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

/--
The main call elimination transformation algorithm on a single statement.
The returned result is a sequence of statements
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
                      := (ListMap.keys proc.header.inputs).zip $ createFvars argTrips.unzip.fst.unzip.fst
        let ret_subst : List (Expression.Ident × Expression.Expr)
                      := (ListMap.keys proc.header.outputs).zip $ createFvars lhs

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

mutual
partial def Block.substFvar (b : Block) (fr:Lambda.Identifier Visibility)
      (to:Lambda.LExpr Lambda.LMonoTy Visibility) : Block :=
  { b with ss := List.map (fun s => Statement.substFvar s fr to) b.ss }

partial def Statement.substFvar (s : Boogie.Statement)
      (fr:Lambda.Identifier Visibility)
      (to:Lambda.LExpr Lambda.LMonoTy Visibility) : Statement :=
  match s with
  | .init lhs ty rhs metadata =>
    .init lhs ty (Lambda.LExpr.substFvar rhs fr to) metadata
  | .set lhs rhs metadata =>
    .set lhs (Lambda.LExpr.substFvar rhs fr to) metadata
  | .havoc _ _ => s
  | .assert lbl b metadata =>
    .assert lbl (Lambda.LExpr.substFvar b fr to) metadata
  | .assume lbl b metadata =>
    .assume lbl (Lambda.LExpr.substFvar b fr to) metadata
  | .call lhs pname args metadata =>
    .call lhs pname (List.map (Lambda.LExpr.substFvar · fr to) args) metadata

  | .block lbl b metadata =>
    .block lbl (Block.substFvar b fr to) metadata
  | .ite cond thenb elseb metadata =>
    .ite (Lambda.LExpr.substFvar cond fr to) (Block.substFvar thenb fr to)
          (Block.substFvar elseb fr to) metadata
  | .loop guard measure invariant body metadata =>
    .loop (Lambda.LExpr.substFvar guard fr to)
          (Option.map (Lambda.LExpr.substFvar · fr to) measure)
          (Option.map (Lambda.LExpr.substFvar · fr to) invariant)
          (Block.substFvar body fr to)
          metadata
  | .goto _ _ => s
end

mutual
partial def Block.renameLhs (b : Block) (fr:String) (to:String) : Block :=
  { b with ss := List.map (fun s => Statement.renameLhs s fr to) b.ss }

partial def Statement.renameLhs (s : Boogie.Statement) (fr:String) (to:String)
    : Statement :=
  match s with
  | .init lhs ty rhs metadata =>
    .init (if lhs.name == fr then { lhs with name := to } else lhs) ty rhs metadata
  | .set lhs rhs metadata =>
    .set (if lhs.name == fr then { lhs with name := to } else lhs) rhs metadata
  | .call lhs pname args metadata =>
    .call (lhs.map (fun l =>
      if l.name == fr  then { l with name := to } else l)) pname args metadata
  | .block lbl b metadata =>
    .block lbl (Block.renameLhs b fr to) metadata
  | .havoc _ _ | .assert _ _ _ | .assume _ _ _ | .ite _ _ _ _
  | .loop _ _ _ _ _ | .goto _ _ => s
end

/--
If st is a call statement, inline the contents of the callee procedure.
This is under the assumption that, the input and output parameters are not
redefined in the procedure body.

For example,

procedure f(x:int) return (y:bool) {
  -- Variables x and y are never redeclared in this scope.
};
-/
def inlineCallStmt (st: Statement) (p : Program)
  : CallElimM (List Statement) :=
    open Lambda in do
    match st with
      | .call lhs procName args _ =>

        let some proc := Program.Procedure.find? p procName
          | throw s!"Procedure {procName} not found in program"

        let sigInputs := LMonoTySignature.toTrivialLTy proc.header.inputs
        let sigOutputs := LMonoTySignature.toTrivialLTy proc.header.outputs

        -- Create a var statement for each LHS variable of the call statement.
        let lhsTrips /-(new id, ty, prev id)-/ ← genOutExprIdentsTrip
          sigOutputs lhs
        let lhsInit := createInitVars
          (lhsTrips.map (fun ((tmpvar,ty),orgvar) => ((orgvar,ty),tmpvar)))

        -- Create a var statement for each procedure input arguments.
        -- Create fresh variable names to avoid name collision.
        -- The input parameter expression is assigned to these new vars.
        let inputTrips ← genArgExprIdentsTrip sigInputs args
        let inputInit := createInits inputTrips

        -- Create a fresh var statement for each procedure output arguments.
        let freshVarsForOutput ← genArgExprIdents (sigOutputs.length)
        let outputTrips ← genOutExprIdentsTrip sigOutputs freshVarsForOutput
        let outputInit := createInitVars
          (outputTrips.map (fun ((tmpvar,ty),orgvar) => ((orgvar,ty),tmpvar)))

        -- Replace all input and output parameters with the fresh variable
        -- names. The code is under the assumption that no local variables
        -- have the same name as input/output parameters.
        let newBody := List.foldl
          (fun body ((new_ident:Expression.Ident), (original_ident,_)) =>
            let new_expr:LExpr LMonoTy Visibility :=
              .fvar new_ident .none
            List.map
              (fun stmt =>
                let st := Statement.substFvar stmt original_ident new_expr
                let res := Statement.renameLhs st original_ident.name
                  new_ident.name
                res
              )
              body)
          proc.body ((inputTrips.unzip.fst.unzip.fst.zip sigInputs) ++
                     (outputTrips.unzip.snd.zip sigOutputs))

        -- Assign the output variables in the signature to the actual output
        -- variables used in the callee.
        let outputSetStmts :=
          let outs_lhs_and_sig := List.zip lhs sigOutputs
          List.map
            (fun (lhs_var,sig_ident,_) =>
              Statement.set lhs_var (.fvar sig_ident (.none)))
            outs_lhs_and_sig

        let stmts:List (Imperative.Stmt Boogie.Expression Boogie.Command)
          := inputInit ++ outputInit ++ newBody ++ outputSetStmts
        let new_blk := Imperative.Block.mk stmts

        return lhsInit ++ [.block (procName ++ "$inlined") new_blk]
      | _ => return [st]

def inlineCallStmts (ss: List Statement) (prog : Program)
  : CallElimM (List Statement) := do match ss with
    | [] => return []
    | s :: ss =>
      let s' := (inlineCallStmt s prog)
      let ss' := (inlineCallStmts ss prog)
      return (← s') ++ (← ss')

def inlineCallL (dcls : List Decl) (prog : Program)
  : CallElimM (List Decl) :=
  match dcls with
  | [] => return []
  | d :: ds =>
    match d with
    | .proc p =>
      return Decl.proc { p with body := ← (inlineCallStmts p.body prog ) } ::
        (← (inlineCallL ds prog))
    | _       => return d :: (← (inlineCallL ds prog))

/--
Procedure calls inlining for an entire program by walking through all
procedure bodies -/
def inlineCall' (p : Program) : CallElimM Program :=
  return { decls := (← (inlineCallL p.decls p)) }


@[simp]
def runWith' {α : Type} (p : α) (f : α → CallElimM β) (s : BoogieGenState):
  Except Err β × BoogieGenState :=
  (StateT.run (f p) s)

@[simp]
def runWith {α : Type} (p : α) (f : α → CallElimM β) (s : BoogieGenState):
  Except Err β :=
  (runWith' p f s).fst

/-- run call elimination with an empty counter state (e.g. starting from 0) -/
@[simp]
def run {α : Type} (p : α) (f : α → CallElimM β):
  Except Err β :=
  runWith p f .emp


end CallElim
end Boogie
