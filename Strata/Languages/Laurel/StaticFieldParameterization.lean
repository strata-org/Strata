/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
import Strata.Util.Tactics

/-!
# Static Field Parameterization Pass

Eliminates `staticFields` from a Laurel `Program` by converting them into
explicit in/out parameters on procedures that read or write them.

Static fields are referenced via `Identifier "$sf_<fieldName>"` identifiers
and written via `Assign [Identifier "$sf_<fieldName>"] value`.

After this pass:
- Procedures that write a static field `f` get both an input `$sf_f` and
  output `$sf_f` parameter (inout pattern).
- Procedures that only read `f` get an input `$sf_f` parameter.
- Call sites are rewritten to pass/receive these parameters.
- `program.staticFields` is set to `[]`.
-/

namespace Strata.Laurel

public section

/-- Prefix for static field parameter names. -/
private def sfPrefix : String := "$sf_"

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }

/-- Check if an identifier name refers to a static field. -/
private def isSFName (name : String) : Bool := name.startsWith sfPrefix

/-- Extract the field name from a `$sf_` prefixed identifier. -/
private def sfFieldName (name : String) : String := (name.drop sfPrefix.length).toString

/-- Analysis result for a single procedure. -/
private structure SFAnalysisResult where
  /-- Static field names read directly (via `$sf_` identifiers). -/
  readsFields : Std.HashSet String := {}
  /-- Static field names written directly (via assignment to `$sf_` identifiers). -/
  writesFields : Std.HashSet String := {}
  /-- Names of callees. -/
  callees : List String := []
  deriving Inhabited

/-- Collect static field reads, writes, and callees from an expression. -/
private partial def collectSFExpr (expr : StmtExprMd) : StateM SFAnalysisResult Unit :=
  match expr.val with
  | .Identifier name =>
    if isSFName name.text then
      modify fun s => { s with readsFields := s.readsFields.insert name.text }
    else pure ()
  | .Assign targets value => do
    for t in targets do
      match t.val with
      | .Identifier name =>
        if isSFName name.text then
          modify fun s => { s with writesFields := s.writesFields.insert name.text }
        else pure ()
      | _ => collectSFExpr t
    collectSFExpr value
  | .StaticCall callee args => do
    modify fun s => { s with callees := callee.text :: s.callees }
    for a in args do collectSFExpr a
  | .IfThenElse c t e => do
    collectSFExpr c; collectSFExpr t
    if let some x := e then collectSFExpr x else pure ()
  | .Block stmts _ => for s in stmts do collectSFExpr s
  | .LocalVariable _ _ i => if let some x := i then collectSFExpr x else pure ()
  | .While c invs d b => do
    collectSFExpr c; collectSFExpr b
    for inv in invs do collectSFExpr inv
    if let some x := d then collectSFExpr x else pure ()
  | .Return v => if let some x := v then collectSFExpr x else pure ()
  | .PrimitiveOp _ args => for a in args do collectSFExpr a
  | .InstanceCall target _ args => do collectSFExpr target; for a in args do collectSFExpr a
  | .ReferenceEquals l r => do collectSFExpr l; collectSFExpr r
  | .AsType t _ => collectSFExpr t
  | .IsType t _ => collectSFExpr t
  | .Forall _ trigger b => do
    if let some t := trigger then collectSFExpr t; collectSFExpr b else collectSFExpr b
  | .Exists _ trigger b => do
    if let some t := trigger then collectSFExpr t; collectSFExpr b else collectSFExpr b
  | .Assigned n => collectSFExpr n
  | .Old v => collectSFExpr v
  | .Fresh v => collectSFExpr v
  | .Assert ⟨c, _⟩ => collectSFExpr c
  | .Assume c => collectSFExpr c
  | .ProveBy v p => do collectSFExpr v; collectSFExpr p
  | .ContractOf _ f => collectSFExpr f
  | .PureFieldUpdate t _ v => do collectSFExpr t; collectSFExpr v
  | _ => pure ()

/-- Analyze a procedure for static field usage. -/
private def analyzeProc (proc : Procedure) : SFAnalysisResult :=
  let bodyResult := match proc.body with
    | .Transparent b => (collectSFExpr b).run ({} : SFAnalysisResult) |>.2
    | .Opaque postconds impl _ =>
      let r1 := postconds.foldl (fun (acc : SFAnalysisResult) (pc : Condition) =>
        let r := (collectSFExpr pc.condition).run ({} : SFAnalysisResult) |>.2
        { readsFields := acc.readsFields.union r.readsFields,
          writesFields := acc.writesFields.union r.writesFields,
          callees := acc.callees ++ r.callees }) ({} : SFAnalysisResult)
      let r2 := match impl with
        | some e => (collectSFExpr e).run ({} : SFAnalysisResult) |>.2
        | none => ({} : SFAnalysisResult)
      { readsFields := r1.readsFields.union r2.readsFields,
        writesFields := r1.writesFields.union r2.writesFields,
        callees := r1.callees ++ r2.callees }
    | .Abstract postconds => (postconds.forM (collectSFExpr ·.condition)).run ({} : SFAnalysisResult) |>.2
    | .External => ({} : SFAnalysisResult)
  let precondResult := (proc.preconditions.forM (collectSFExpr ·.condition)).run ({} : SFAnalysisResult) |>.2
  { readsFields := bodyResult.readsFields.union precondResult.readsFields,
    writesFields := bodyResult.writesFields.union precondResult.writesFields,
    callees := bodyResult.callees ++ precondResult.callees }

/-- Compute the transitive closure of which procedures read static fields. -/
private def computeFieldReaders (procs : List Procedure) (sfNames : List String)
    : Std.HashMap String (Std.HashSet String) :=
  let info := procs.map fun p => (p.name.text, analyzeProc p)
  let direct : Std.HashMap String (Std.HashSet String) := info.foldl (fun acc (name, r) =>
    let fields := sfNames.foldl (fun fs f =>
      if r.readsFields.contains f || r.writesFields.contains f then fs.insert f else fs) {}
    if fields.isEmpty then acc else acc.insert name fields) {}
  let rec fixpoint (fuel : Nat) (current : Std.HashMap String (Std.HashSet String))
      : Std.HashMap String (Std.HashSet String) :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.foldl (fun acc (name, r) =>
        let existing := acc[name]?.getD {}
        let fromCallees := r.callees.foldl (fun fs callee =>
          match acc[callee]? with
          | some calleeFields => fs.union calleeFields
          | none => fs) existing
        if fromCallees.isEmpty then acc else acc.insert name fromCallees) current
      if next.toList.length == current.toList.length then current
      else fixpoint fuel' next
  fixpoint procs.length direct

/-- Compute the transitive closure of which procedures write static fields. -/
private def computeFieldWriters (procs : List Procedure) (sfNames : List String)
    : Std.HashMap String (Std.HashSet String) :=
  let info := procs.map fun p => (p.name.text, analyzeProc p)
  let direct : Std.HashMap String (Std.HashSet String) := info.foldl (fun acc (name, r) =>
    let fields := sfNames.foldl (fun fs f =>
      if r.writesFields.contains f then fs.insert f else fs) {}
    if fields.isEmpty then acc else acc.insert name fields) {}
  let rec fixpoint (fuel : Nat) (current : Std.HashMap String (Std.HashSet String))
      : Std.HashMap String (Std.HashSet String) :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.foldl (fun acc (name, r) =>
        let existing := acc[name]?.getD {}
        let fromCallees := r.callees.foldl (fun fs callee =>
          match acc[callee]? with
          | some calleeFields => fs.union calleeFields
          | none => fs) existing
        if fromCallees.isEmpty then acc else acc.insert name fromCallees) current
      if next.toList.length == current.toList.length then current
      else fixpoint fuel' next
  fixpoint procs.length direct

/-- State for the static field transform. -/
private structure SFTransformState where
  fieldReaders : Std.HashMap String (Std.HashSet String)
  fieldWriters : Std.HashMap String (Std.HashSet String)
  sfNames : List String
  /-- Map from `$sf_` name to the field's type. -/
  sfTypes : Std.HashMap String HighTypeMd := {}
  freshCounter : Nat := 0

private abbrev SFTransformM := StateM SFTransformState

private def sfFreshVarName : SFTransformM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$sftmp{s.freshCounter}"

/-- Look up the type for a `$sf_` name, defaulting to Unknown. -/
private def sfType (name : String) : SFTransformM HighTypeMd := do
  let s ← get
  return s.sfTypes[name]?.getD ⟨.Unknown, none, .empty⟩

/-- Get the sorted list of `$sf_` names a procedure reads (directly or transitively). -/
private def procReadsFields (procName : String) : SFTransformM (List String) := do
  let s ← get
  let fields := s.fieldReaders[procName]?.getD {}
  return s.sfNames.filter fields.contains

/-- Get the sorted list of `$sf_` names a procedure writes (directly or transitively). -/
private def procWritesFields (procName : String) : SFTransformM (List String) := do
  let s ← get
  let fields := s.fieldWriters[procName]?.getD {}
  return s.sfNames.filter fields.contains

/-- Transform an expression, rewriting call sites to pass/receive static field parameters. -/
private partial def sfTransformExpr (expr : StmtExprMd) (valueUsed : Bool := true) : SFTransformM StmtExprMd := do
  let ⟨e, source, md⟩ := expr
  match e with
  | .StaticCall callee args => do
    let args' ← args.mapM sfTransformExpr
    let calleeReads ← procReadsFields callee.text
    let calleeWrites ← procWritesFields callee.text
    if calleeWrites.isEmpty && calleeReads.isEmpty then
      return ⟨.StaticCall callee args', source, md⟩
    else if !calleeWrites.isEmpty then
      -- Pass current $sf_ values as input args, receive updated values as output
      let inParams := calleeReads.map fun f => mkMd (.Identifier (mkId f))
      let callExpr := ⟨.StaticCall callee (inParams ++ args'), source, md⟩
      let outFields := calleeWrites
      if valueUsed then
        let freshVar ← sfFreshVarName
        let varDecl := mkMd (.LocalVariable freshVar ⟨.Unknown, none, .empty⟩ none)
        let outTargets := outFields.map fun f => mkMd (.Identifier (mkId f))
        let assignStmt := ⟨.Assign (outTargets ++ [mkMd (.Identifier freshVar)]) callExpr, source, md⟩
        return ⟨.Block [varDecl, assignStmt, mkMd (.Identifier freshVar)] none, source, md⟩
      else
        let outTargets := outFields.map fun f => mkMd (.Identifier (mkId f))
        return ⟨.Assign outTargets callExpr, source, md⟩
    else
      -- Callee only reads: pass current $sf_ values as input args
      let inParams := calleeReads.map fun f => mkMd (.Identifier (mkId f))
      return ⟨.StaticCall callee (inParams ++ args'), source, md⟩
  | .IfThenElse c t el => do
    let el' ← match el with | some x => some <$> sfTransformExpr x valueUsed | none => pure none
    return ⟨.IfThenElse (← sfTransformExpr c) (← sfTransformExpr t valueUsed) el', source, md⟩
  | .Block stmts label => do
    let n := stmts.length
    let rec processStmts (idx : Nat) (remaining : List StmtExprMd) : SFTransformM (List StmtExprMd) := do
      match remaining with
      | [] => pure []
      | s :: rest =>
        let isLast := idx == n - 1
        let s' ← sfTransformExpr s (isLast && valueUsed)
        let rest' ← processStmts (idx + 1) rest
        pure (s' :: rest')
    return ⟨.Block (← processStmts 0 stmts) label, source, md⟩
  | .LocalVariable n ty i => do
    let i' ← match i with | some x => some <$> sfTransformExpr x | none => pure none
    return ⟨.LocalVariable n ty i', source, md⟩
  | .While c invs d b => do
    let invs' ← invs.mapM sfTransformExpr
    return ⟨.While (← sfTransformExpr c) invs' d (← sfTransformExpr b false), source, md⟩
  | .Return v => do
    let v' ← match v with | some x => some <$> sfTransformExpr x | none => pure none
    return ⟨.Return v', source, md⟩
  | .Assign targets value => do
    let targets' ← targets.mapM sfTransformExpr
    return ⟨.Assign targets' (← sfTransformExpr value), source, md⟩
  | .PrimitiveOp op args => do
    return ⟨.PrimitiveOp op (← args.mapM sfTransformExpr), source, md⟩
  | .InstanceCall target callee args => do
    return ⟨.InstanceCall (← sfTransformExpr target) callee (← args.mapM sfTransformExpr), source, md⟩
  | .FieldSelect target fieldName =>
    return ⟨.FieldSelect (← sfTransformExpr target) fieldName, source, md⟩
  | .PureFieldUpdate t f v => do
    return ⟨.PureFieldUpdate (← sfTransformExpr t) f (← sfTransformExpr v), source, md⟩
  | .ReferenceEquals l r => do
    return ⟨.ReferenceEquals (← sfTransformExpr l) (← sfTransformExpr r), source, md⟩
  | .AsType t ty => return ⟨.AsType (← sfTransformExpr t valueUsed) ty, source, md⟩
  | .IsType t ty => return ⟨.IsType (← sfTransformExpr t) ty, source, md⟩
  | .Forall p trigger b => do
    let trigger' ← trigger.mapM sfTransformExpr
    return ⟨.Forall p trigger' (← sfTransformExpr b), source, md⟩
  | .Exists p trigger b => do
    let trigger' ← trigger.mapM sfTransformExpr
    return ⟨.Exists p trigger' (← sfTransformExpr b), source, md⟩
  | .Assigned n => return ⟨.Assigned (← sfTransformExpr n), source, md⟩
  | .Old v => return ⟨.Old (← sfTransformExpr v), source, md⟩
  | .Fresh v => return ⟨.Fresh (← sfTransformExpr v), source, md⟩
  | .Assert ⟨condExpr, summary⟩ =>
    return ⟨.Assert { condition := ← sfTransformExpr condExpr, summary }, source, md⟩
  | .Assume c => return ⟨.Assume (← sfTransformExpr c), source, md⟩
  | .ProveBy v p => do return ⟨.ProveBy (← sfTransformExpr v) (← sfTransformExpr p), source, md⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← sfTransformExpr f), source, md⟩
  | _ => return expr

/-- Remove `$sf_` local variable declarations from a block's top-level statements. -/
private def stripSFLocalDecls (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .Block stmts label =>
    let stmts' := stmts.filter fun s =>
      match s.val with
      | .LocalVariable name _ _ => !isSFName name.text
      | _ => true
    { expr with val := .Block stmts' label }
  | _ => expr

/-- Transform a procedure: add static field parameters and rewrite call sites in the body. -/
private def sfTransformProcedure (proc : Procedure) : SFTransformM Procedure := do
  let reads ← procReadsFields proc.name.text
  let writes ← procWritesFields proc.name.text
  if reads.isEmpty && writes.isEmpty then return proc

  let bodyValueIsUsed := !proc.outputs.isEmpty
  let body' ← match proc.body with
    | .Transparent bodyExpr =>
      pure (.Transparent (← sfTransformExpr bodyExpr bodyValueIsUsed))
    | .Opaque postconds impl modif =>
      let postconds' ← postconds.mapM (·.mapM sfTransformExpr)
      let impl' ← impl.mapM (sfTransformExpr · bodyValueIsUsed)
      let modif' ← modif.mapM sfTransformExpr
      pure (.Opaque postconds' impl' modif')
    | .Abstract postconds =>
      let postconds' ← postconds.mapM (·.mapM sfTransformExpr)
      pure (.Abstract postconds')
    | .External => pure .External

  let preconditions' ← proc.preconditions.mapM (·.mapM sfTransformExpr)

  -- __main__ keeps $sf_ as local variables; other procedures get them as parameters
  if proc.name.text == "__main__" then
    return { proc with preconditions := preconditions', body := body' }

  -- Add input parameters for all fields this procedure reads (includes writes)
  let inParamPrefix := "$sf_in_"
  let mut inParams : List Parameter := []
  for f in reads do
    let ty ← sfType f
    inParams := inParams ++ [{ name := mkId (inParamPrefix ++ sfFieldName f), type := ty }]
  -- Add output parameters for fields this procedure writes
  let mut outParams : List Parameter := []
  for f in writes do
    let ty ← sfType f
    outParams := outParams ++ [{ name := mkId f, type := ty }]

  let inputs' := inParams ++ proc.inputs
  let outputs' := outParams ++ proc.outputs

  -- At the start of the body, assign input parameter values to local $sf_ variables
  -- and strip the $sf_ local variable declarations (they're now parameters)
  let paramAssigns := reads.map fun f =>
    mkMd (.Assign [mkMd (.Identifier (mkId f))] (mkMd (.Identifier (mkId (inParamPrefix ++ sfFieldName f)))))

  let body' := match body' with
    | .Transparent bodyExpr =>
      let bodyExpr' := stripSFLocalDecls bodyExpr
      .Transparent (mkMd (.Block (paramAssigns ++ [bodyExpr']) none))
    | .Opaque postconds (some impl) modif =>
      let impl' := stripSFLocalDecls impl
      .Opaque postconds (some (mkMd (.Block (paramAssigns ++ [impl']) none))) modif
    | other => other

  return { proc with
    inputs := inputs',
    outputs := outputs',
    preconditions := preconditions',
    body := body' }

/-- Run the static field parameterization pass on a program.
    Eliminates `staticFields` by converting them to explicit procedure parameters. -/
def staticFieldParameterization (program : Program) : Program :=
  if program.staticFields.isEmpty then program
  else
    let sfNames := program.staticFields.map (fun f => sfPrefix ++ f.name.text) |>.mergeSort
    let sfTypes : Std.HashMap String HighTypeMd := program.staticFields.foldl
      (fun m f => m.insert (sfPrefix ++ f.name.text) f.type) {}
    let fieldReaders := computeFieldReaders program.staticProcedures sfNames
    let fieldWriters := computeFieldWriters program.staticProcedures sfNames
    let initState : SFTransformState := { fieldReaders, fieldWriters, sfNames, sfTypes }
    let (procs', _) := (program.staticProcedures.mapM sfTransformProcedure).run initState
    { program with
      staticProcedures := procs',
      staticFields := [] }

end -- public section
end Strata.Laurel
