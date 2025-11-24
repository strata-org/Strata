/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Transform.BoogieTransform
import Strata.Languages.Boogie.Statement
import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.OldExpressions
import Strata.Languages.Boogie.ProgramWF
import Strata.DL.Util.ListUtils
import Strata.Languages.Boogie.BoogieGen
import Strata.DL.Util.LabelGen

/-! # Procedure Inlining Transformation -/

namespace Boogie
namespace ProcedureInlining

open Transform

/-
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
-/

mutual
partial def Block.substFvar (b : Block) (fr:Expression.Ident)
      (to:Expression.Expr) : Block :=
  { b with ss := List.map (fun s => Statement.substFvar s fr to) b.ss }

partial def Statement.substFvar (s : Boogie.Statement)
      (fr:Expression.Ident)
      (to:Expression.Expr) : Statement :=
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
partial def Block.renameLhs (b : Block) (fr: Lambda.Identifier Visibility) (to: Lambda.Identifier Visibility) : Block :=
  { b with ss := List.map (fun s => Statement.renameLhs s fr to) b.ss }

partial def Statement.renameLhs (s : Boogie.Statement) (fr: Lambda.Identifier Visibility) (to: Lambda.Identifier Visibility)
    : Statement :=
  match s with
  | .init lhs ty rhs metadata =>
    .init (if lhs.name == fr then to else lhs) ty rhs metadata
  | .set lhs rhs metadata =>
    .set (if lhs.name == fr then to else lhs) rhs metadata
  | .call lhs pname args metadata =>
    .call (lhs.map (fun l =>
      if l.name == fr  then to else l)) pname args metadata
  | .block lbl b metadata =>
    .block lbl (Block.renameLhs b fr to) metadata
  | .havoc _ _ | .assert _ _ _ | .assume _ _ _ | .ite _ _ _ _
  | .loop _ _ _ _ _ | .goto _ _ => s
end

-- Unlike Stmt.hasLabel, this gathers labels in assert and assume as well.
mutual
partial def Block.labels (b : Block): List String :=
  List.flatMap (fun s => Statement.labels s) b.ss

-- Assume and Assert's labels have special meanings, so they must not be
-- mangled during procedure inlining.
partial def Statement.labels (s : Boogie.Statement) : List String :=
  match s with
  | .block lbl b _ => lbl :: (Block.labels b)
  | .ite _ thenb elseb _ => (Block.labels thenb) ++ (Block.labels elseb)
  | .loop _ _ _ body _ => Block.labels body
  | _ => []
end

mutual
partial def Block.replaceLabels (b : Block) (map:Map String String)
    : Block :=
   { b with ss := b.ss.map (fun s => Statement.replaceLabels s map) }

partial def Statement.replaceLabels
    (s : Boogie.Statement) (map:Map String String) : Boogie.Statement :=
  let app (s:String) :=
    match Map.find? map s with
    | .none => s
    | .some s' => s'
  match s with
  | .block lbl b m => .block (app lbl) (Block.replaceLabels b map) m
  | .goto lbl m => .goto (app lbl) m
  | .ite cond thenb elseb _ =>
    .ite cond (Block.replaceLabels thenb map) (Block.replaceLabels elseb map)
  | .loop g measure inv body m =>
    .loop g measure inv (Block.replaceLabels body map) m
  | _ => s
end


private def genOldToFreshIdMappings (old_vars : List Expression.Ident)
    (prev_map : Map Expression.Ident Expression.Ident) (prefix_ : String)
    : BoogieTransformM (Map Expression.Ident Expression.Ident) := do
  let prev_map <- old_vars.foldlM
    (fun var_map id => do
      let new_name <- genIdent id (fun s => prefix_ ++ "_" ++ s)
      return var_map.insert id new_name)
    prev_map
  return prev_map

private def renameAllLocalNames (c:Procedure)
    : BoogieTransformM (Procedure × Map Expression.Ident Expression.Ident) := do
  let var_map: Map Expression.Ident Expression.Ident := []
  let proc_name := c.header.name.name

  -- Make a map for renaming local variables
  let lhs_vars := List.flatMap (fun (s:Statement) => s.definedVars) c.body
  let lhs_vars := lhs_vars ++ c.header.inputs.unzip.fst ++
                  c.header.outputs.unzip.fst
  let var_map <- genOldToFreshIdMappings lhs_vars var_map proc_name

  -- Make a map for renaming label names
  let labels := List.flatMap (fun s => Statement.labels s) c.body
  -- Reuse genOldToFreshIdMappings by introducing dummy data to Identifier
  let label_ids:List Expression.Ident := labels.map
      (fun s => { name:=s, metadata := Visibility.temp })
  let label_map_id <- genOldToFreshIdMappings label_ids [] proc_name
  let label_map := label_map_id.map (fun (id1,id2) => (id1.name, id2.name))

  -- Do substitution
  let new_body := List.map (fun (s0:Statement) =>
    var_map.foldl (fun (s:Statement) (old_id,new_id) =>
        let s := Statement.substFvar s old_id (.fvar () new_id .none)
        let s := Statement.renameLhs s old_id new_id
        Statement.replaceLabels s label_map)
      s0) c.body
  let new_header := { c.header with
    inputs := c.header.inputs.map (fun (id,ty) =>
      match var_map.find? id with
      | .some id' => (id',ty)
      | .none => panic! "unreachable"),
    outputs := c.header.outputs.map (fun (id,ty) =>
      match var_map.find? id with
      | .some id' => (id',ty)
      | .none => panic! "unreachable")
    }
  return ({ c with body := new_body, header := new_header }, var_map)


/-
Procedure Inlining.

If st is a call statement, inline the contents of the callee procedure.
To avoid conflicts between duplicated variable names in caller and callee,
every variables in callee are renamed.
This function does not update the specification because inlineCallStmt will not
use the specification. This will have to change if Strata also wants to support
the reachability query.
-/
def inlineCallStmt (st: Statement) (p : Program)
  : BoogieTransformM (List Statement) :=
    open Lambda in do
    match st with
      | .call lhs procName args _ =>

        let some proc := Program.Procedure.find? p procName
          | throw s!"Procedure {procName} not found in program"

        -- Create a copy of the procedure that has all input/output/local vars
        -- replaced with fresh ones
        let (proc,var_map) <- renameAllLocalNames proc

        let sigOutputs := LMonoTySignature.toTrivialLTy proc.header.outputs
        let sigInputs := LMonoTySignature.toTrivialLTy proc.header.inputs

        -- Stuffs for the call statement:
        --   call x1,x2, .. = f(v1,v2,...)
        --   where 'procedure f(in1,in2,..) outputs(out1,out2,..)'
        -- Insert
        --   init in1 : ty := v1     --- inputInit
        --   init in2 : ty := v2
        --   init out1 : ty := <placeholder> --- outputInit
        --   init out2 : ty := <placeholder>
        --   ... (f body)
        --   set x1 := out1    --- outputSetStmts
        --   set x2 := out2
        -- `init outN` is not necessary because calls are only allowed to use
        -- already declared variables (per Boogie.typeCheck)

        -- Create a fresh var statement for each LHS
        let outputTrips ← genOutExprIdentsTrip sigOutputs sigOutputs.unzip.fst
        let outputInit := createInitVars
          (outputTrips.map (fun ((tmpvar,ty),orgvar) => ((orgvar,ty),tmpvar)))
        -- Create a var statement for each procedure input arguments.
        -- The input parameter expression is assigned to these new vars.
        let inputTrips ← genArgExprIdentsTrip sigInputs args
        let inputInit := createInits inputTrips
        -- Assign the output variables in the signature to the actual output
        -- variables used in the callee.
        let outputSetStmts :=
          let out_vars := sigOutputs.unzip.fst
          let out_vars := out_vars.map
              (fun id => match var_map.find? id with
                  | .none => id | .some x => x)
          let outs_lhs_and_sig := List.zip lhs out_vars
          List.map
            (fun (lhs_var,out_var) =>
              Statement.set lhs_var (.fvar () out_var (.none)))
            outs_lhs_and_sig

        let stmts:List (Imperative.Stmt Boogie.Expression Boogie.Command)
          := inputInit ++ outputInit ++ proc.body ++ outputSetStmts
        let new_blk := Imperative.Block.mk stmts

        return [.block (procName ++ "$inlined") new_blk]
      | _ => return [st]

def inlineCallStmts (ss: List Statement) (prog : Program)
  : BoogieTransformM (List Statement) := do match ss with
    | [] => return []
    | s :: ss =>
      let s' := (inlineCallStmt s prog)
      let ss' := (inlineCallStmts ss prog)
      return (← s') ++ (← ss')

def inlineCallL (dcls : List Decl) (prog : Program)
  : BoogieTransformM (List Decl) :=
  match dcls with
  | [] => return []
  | d :: ds =>
    match d with
    | .proc p =>
      return Decl.proc { p with body := ← (inlineCallStmts p.body prog ) } ::
        (← (inlineCallL ds prog))
    | _       => return d :: (← (inlineCallL ds prog))

end ProcedureInlining
end Boogie
