/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.LabelGen
import Strata.DL.Util.ListUtils
import Strata.Languages.Core.Core
import Strata.Languages.Core.CoreGen
import Strata.Languages.Core.ProgramWF
import Strata.Languages.Core.Statement
import Strata.Transform.CoreTransform
import Strata.Util.Tactics

/-! # Procedure Inlining Transformation -/

namespace Core
namespace ProcedureInlining

open Transform

-- Unlike Stmt.hasLabel, this gathers labels in assert and assume as well.
mutual
def Block.labels (b : Block): List String :=
  List.flatMap (fun s => Statement.labels s) b

def Statement.labels (s : Core.Statement) : List String :=
  match s with
  | .block lbl b _ => lbl :: (Block.labels b)
  | .ite _ thenb elseb _ => (Block.labels thenb) ++ (Block.labels elseb)
  | .loop _ _ _ body _ => Block.labels body
  | .assume lbl _ _ => [lbl]
  | .assert lbl _ _ => [lbl]
  | .cover lbl _ _ => [lbl]
  | .goto _ _ => []
  -- No other labeled commands.
  | .cmd _ => []
  | .funcDecl _ _ => []
end

mutual
def Block.replaceLabels (b : Block) (map:Map String String)
    : Block :=
  b.map (fun s => Statement.replaceLabels s map)

def Statement.replaceLabels
    (s : Core.Statement) (map:Map String String) : Core.Statement :=
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
  | .assume lbl e m => .assume (app lbl) e m
  | .assert lbl e m => .assert (app lbl) e m
  | .cover lbl e m => .cover (app lbl) e m
  | .cmd _ => s
  | .funcDecl _ _ => s
end


private def genOldToFreshIdMappings (old_vars : List Expression.Ident)
    (prev_map : Map Expression.Ident Expression.Ident) (prefix_ : String)
    : CoreTransformM (Map Expression.Ident Expression.Ident) := do
  let prev_map <- old_vars.foldlM
    (fun var_map id => do
      let new_name <- genIdent id (fun s => prefix_ ++ "_" ++ s)
      return var_map.insert id new_name)
    prev_map
  return prev_map

private def renameAllLocalNames (c:Procedure)
    : CoreTransformM (Procedure × Map Expression.Ident Expression.Ident) := do
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


/-- Update the call graph after inlining one f(caller) -> g(callee) invocation. -/
def updateCallGraph (cg:CallGraph) (f: String) (g: String):
    Except Err CallGraph := do
  -- For each edge 'g -> x', add f -> x'
  let edges_from_g ← match cg.callees.get? g with
    | .some r => .ok r
    | .none => throw s!"Invalid CallGraph: can't find {g} from callees domain"
  let edges_from_f ← match cg.callees.get? f with
    | .some r => .ok r
    | .none => throw s!"Invalid CallGraph: can't find {f} from callees domain"
  let edges_from_f := edges_from_g.fold
    (fun (edges_from_f:Std.HashMap String Nat) fn_x cnt =>
      edges_from_f.alter fn_x (fun v =>
        .some (match v with | .none => cnt | .some v' => cnt + v')))
    edges_from_f
  let callees_new := cg.callees.insert f edges_from_f

  -- Now the callers. For every 'g -> x' edge, add f -> x'.
  let callers_new ← edges_from_g.foldM
    (fun (m:Std.HashMap String (Std.HashMap String Nat)) fn_x cnt => do
      match m.get? fn_x with
      | .none => throw s!"Invalid CallGraph: can't find {fn_x} from callers domain"
      | .some edges_to_x =>
        .ok (m.insert fn_x (edges_to_x.alter f (fun v =>
          .some (match v with | .none => cnt | .some v' => cnt + v')))))
    cg.callers

  let cg_new : CallGraph := { callees := callees_new, callers := callers_new }

  -- .. and decrement the 'f -> g' edge by 1.
  let cg_final ← cg_new.decrementEdge f g
  return cg_final

/-
Procedure Inlining.

If st is a call statement, inline the contents of the callee procedure.
To avoid conflicts between duplicated variable names in caller and callee,
every variables in callee are renamed.
This function does not update the specification because inlineCallStmt will not
use the specification. This will have to change if Strata also wants to support
the reachability query.
-/
def inlineCallCmd
    (doInline:String -> CachedAnalyses -> Bool := λ _ _ => true)
    (cmd: Command)
  : CoreTransformM (Option (List Statement)) :=
    open Lambda in do
    match cmd with
      | .call lhs procName args _ =>

        let st ← get
        if ¬ doInline procName st.cachedAnalyses then return .none else

        let some p := (← get).currentProgram
          | throw s!"currentProgram not set"
        let some currProcName := (← get).currentProcedureName
          | throw s!"currentProcedure not set"
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
        -- already declared variables (per Core.typeCheck)

        -- Create a fresh var statement for each LHS
        let outputTrips ← genOutExprIdentsTrip sigOutputs sigOutputs.unzip.fst
        let outputInits := createInitVars
          (outputTrips.map (fun ((tmpvar,ty),orgvar) => ((orgvar,ty),tmpvar)))
        let outputHavocs := outputTrips.map (fun
          (_,orgvar) => Statement.havoc orgvar)
        -- Create a var statement for each procedure input arguments.
        -- The input parameter expression is assigned to these new vars.
        --let inputTrips ← genArgExprIdentsTrip sigInputs args
        let inputInits := createInits (sigInputs.zip args)
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

        let stmts:List (Imperative.Stmt Core.Expression Core.Command)
          := inputInits ++ outputInits ++ outputHavocs ++ proc.body ++
             outputSetStmts

        -- Update CallGraph if available
        let σ ← get
        match σ.cachedAnalyses.callGraph with
        | .none => modify id -- do nothing
        | .some callGraph =>
          let callGraph' ← updateCallGraph callGraph currProcName procName
          set ({ σ with
            cachedAnalyses := {
              callGraph := .some callGraph'
            }
          }:CoreTransformState)

        return .some [.block (procName ++ "$inlined") stmts]

      | _ => return .none

end ProcedureInlining
end Core
