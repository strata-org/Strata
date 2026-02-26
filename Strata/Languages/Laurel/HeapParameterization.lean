/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Languages.Laurel.LaurelTypes
import Strata.Util.Tactics

/-
Heap Parameterization Pass

Transforms procedures that interact with the heap by adding explicit heap parameters.
The heap is modeled as a `Heap` datatype containing a `data: Map Composite (Map Field Box)` map
and a `nextReference: int` for allocating new objects. Box is a sum type with constructors for each
primitive type (BoxInt, BoxBool, BoxFloat64, BoxComposite). Composite is a type synonym for int.

1. Procedures that write the heap get an inout heap parameter
   - Input: `heap : THeap`
   - Output: `heap : THeap`
   - Field writes become: `heap := updateField(heap, obj, field, BoxT(value))`

2. Procedures that only read the heap get an in heap parameter
   - Input: `heap : THeap`
   - Field reads become: `Box..tVal(readField(heap, obj, field))`

3. Procedure calls are transformed:
   - Calls to heap-writing procedures in expressions:
     `f(args...) => (var freshVar: type; heapVar, freshVar := f(heapVar, args...); freshVar)`
   - Calls to heap-writing procedures as statements:
     `f(args...)` => `heap := f(heap, args...)`
   - Calls to heap-reading procedures:
     `f(args...)` => `f(heap, args...)`

The analysis is transitive: if procedure A calls procedure B, and B reads/writes the heap,
then A is also considered to read/write the heap.
-/

namespace Strata.Laurel

structure AnalysisResult where
  readsHeapDirectly : Bool := false
  writesHeapDirectly : Bool := false
  callees : List Identifier := []


mutual
def collectExprMd (expr : StmtExprMd) : StateM AnalysisResult Unit := collectExpr expr.val
  termination_by sizeOf expr
  decreasing_by cases expr; term_by_mem

def collectExpr (expr : StmtExpr) : StateM AnalysisResult Unit := do
  match _: expr with
  | .FieldSelect target _ =>
      modify fun s => { s with readsHeapDirectly := true }; collectExprMd target
  | .InstanceCall target _ args => collectExprMd target; for a in args do collectExprMd a
  | .StaticCall callee args => modify fun s => { s with callees := callee :: s.callees }; for a in args do collectExprMd a
  | .IfThenElse c t e => collectExprMd c; collectExprMd t; if let some x := e then collectExprMd x
  | .Block stmts _ => for s in stmts do collectExprMd s
  | .LocalVariable _ _ i => if let some x := i then collectExprMd x
  | .While c invs d b => collectExprMd c; collectExprMd b; for inv in invs do collectExprMd inv; if let some x := d then collectExprMd x
  | .Return v => if let some x := v then collectExprMd x
  | .Assign assignTargets v =>
      -- Check if any target is a field assignment (heap write)
      for ⟨assignTarget, _⟩ in assignTargets.attach do
        match assignTarget.val with
        | .FieldSelect _ _ =>
            modify fun s => { s with writesHeapDirectly := true }
        | _ => pure ()
        collectExprMd assignTarget
      collectExprMd v
  | .PureFieldUpdate t _ v => collectExprMd t; collectExprMd v
  | .PrimitiveOp _ args => for a in args do collectExprMd a
  | .New _ => modify fun s => { s with writesHeapDirectly := true }
  | .ReferenceEquals l r => collectExprMd l; collectExprMd r
  | .AsType t _ => collectExprMd t
  | .IsType t _ => collectExprMd t
  | .Forall _ _ b => collectExprMd b
  | .Exists _ _ b => collectExprMd b
  | .Assigned n => collectExprMd n
  | .Old v => collectExprMd v
  | .Fresh v => collectExprMd v
  | .Assert c => collectExprMd c
  | .Assume c => collectExprMd c
  | .ProveBy v p => collectExprMd v; collectExprMd p
  | .ContractOf _ f => collectExprMd f
  | _ => pure ()
  termination_by sizeOf expr
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

def analyzeProc (proc : Procedure) : AnalysisResult :=
  let bodyResult := match proc.body with
    | .Transparent b => (collectExprMd b).run {} |>.2
    | .Opaque postconds impl modif =>
        -- A non-empty modifies clause implies the procedure reads and writes the heap;
        -- no need to inspect the body further in that case.
        if !modif.isEmpty then
          { readsHeapDirectly := true, writesHeapDirectly := true, callees := [] }
        else
          let r1 := postconds.foldl (fun (acc : AnalysisResult) pc =>
            let r := (collectExprMd pc).run {} |>.2
            { readsHeapDirectly := acc.readsHeapDirectly || r.readsHeapDirectly,
              writesHeapDirectly := acc.writesHeapDirectly || r.writesHeapDirectly,
              callees := acc.callees ++ r.callees }) {}
          let r2 := match impl with
            | some e => (collectExprMd e).run {} |>.2
            | none => {}
          { readsHeapDirectly := r1.readsHeapDirectly || r2.readsHeapDirectly,
            writesHeapDirectly := r1.writesHeapDirectly || r2.writesHeapDirectly,
            callees := r1.callees ++ r2.callees }
    | .Abstract postconds => (postconds.forM collectExprMd).run {} |>.2
  -- Also analyze preconditions
  let precondResult := (proc.preconditions.forM collectExprMd).run {} |>.2
  { readsHeapDirectly := bodyResult.readsHeapDirectly || precondResult.readsHeapDirectly,
    writesHeapDirectly := bodyResult.writesHeapDirectly || precondResult.writesHeapDirectly,
    callees := bodyResult.callees ++ precondResult.callees }

def computeReadsHeap (procs : List Procedure) : List Identifier :=
  let info := procs.map fun p => (p.name, analyzeProc p)
  let direct := info.filterMap fun (n, r) => if r.readsHeapDirectly then some n else none
  let rec fixpoint (fuel : Nat) (current : List Identifier) : List Identifier :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.filterMap fun (n, r) =>
        if current.contains n then some n
        else if r.callees.any current.contains then some n
        else none
      if next.length == current.length then current else fixpoint fuel' next
  fixpoint procs.length direct

def computeWritesHeap (procs : List Procedure) : List Identifier :=
  let info := procs.map fun p => (p.name, analyzeProc p)
  let direct := info.filterMap fun (n, r) => if r.writesHeapDirectly then some n else none
  let rec fixpoint (fuel : Nat) (current : List Identifier) : List Identifier :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.filterMap fun (n, r) =>
        if current.contains n then some n
        else if r.callees.any current.contains then some n
        else none
      if next.length == current.length then current else fixpoint fuel' next
  fixpoint procs.length direct

structure TransformState where
  fieldConstants : List Constant := []
  heapReaders : List Identifier
  heapWriters : List Identifier
  fieldTypes : List (Identifier × HighTypeMd) := []  -- Maps "TypeName.fieldName" to their value types
  types : List TypeDefinition := []  -- Type definitions for resolving field owners
  freshCounter : Nat := 0  -- Counter for generating fresh variable names

abbrev TransformM := StateM TransformState

def addFieldConstant (name : Identifier) (valueType : HighTypeMd) : TransformM Unit :=
  modify fun s => if s.fieldConstants.any (·.name == name) then s
    else { s with fieldConstants := { name := name, type := ⟨.TTypedField valueType, #[] ⟩ } :: s.fieldConstants }

def lookupFieldType (name : Identifier) : TransformM (Option HighTypeMd) := do
  return (← get).fieldTypes.find? (·.1 == name) |>.map (·.2)

/-- Get the Box destructor name for a given Laurel HighType -/
def boxDestructorName (ty : HighType) : Identifier :=
  match ty with
  | .TInt => "Box..intVal"
  | .TBool => "Box..boolVal"
  | .TFloat64 => "Box..float64Val"
  | .UserDefined _ => "Box..compositeVal"
  | _ => "Box..intVal"  -- fallback

/-- Get the Box constructor name for a given Laurel HighType -/
def boxConstructorName (ty : HighType) : Identifier :=
  match ty with
  | .TInt => "BoxInt"
  | .TBool => "BoxBool"
  | .TFloat64 => "BoxFloat64"
  | .UserDefined _ => "BoxComposite"
  | _ => "BoxInt"  -- fallback

def readsHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapReaders.contains name

def writesHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapWriters.contains name

def freshVarName : TransformM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$tmp{s.freshCounter}"

/-- Helper to wrap a StmtExpr into StmtExprMd with empty metadata -/
private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

/--
Find the composite type that actually declares a given field, walking up the inheritance chain.
Returns the declaring type's name, or falls back to the given type name.
-/
def findFieldOwner (types : List TypeDefinition) (typeName : Identifier) (fieldName : Identifier) : Identifier :=
  let rec go (fuel : Nat) (current : Identifier) : Option Identifier :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      types.findSome? fun td =>
        match td with
        | .Composite ct =>
          if ct.name == current then
            if ct.fields.any (·.name == fieldName) then some ct.name
            else ct.extending.findSome? (go fuel')
          else none
        | _ => none
  (go types.length typeName).getD (panic "type inheritance forms a cycle")

/--
Resolve the owning composite type name for a field access by computing the target expression's type.
Returns the qualified field name "DeclaringType.fieldName".
-/
def resolveQualifiedFieldName (env : TypeEnv) (types : List TypeDefinition) (target : StmtExprMd) (fieldName : Identifier) : Identifier :=
  match (computeExprType env types target).val with
  | .UserDefined typeName =>
    let owner := findFieldOwner types typeName fieldName
    owner ++ "." ++ fieldName
  | _ => panic "assigning to a target that's not a composite type"

/--
Transform an expression, adding heap parameters where needed.
- `heapVar`: the name of the heap variable to use
- `env`: the type environment for resolving field owners
- `valueUsed`: whether the result value of this expression is used (affects optimization of heap-writing calls)
-/
def heapTransformExpr (heapVar : Identifier) (env : TypeEnv) (expr : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd :=
  recurse env expr valueUsed
where
  recurse (env : TypeEnv) (expr : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd := do
    let md := expr.md
    let types := (← get).types
    match _h : expr.val with
    | .FieldSelect selectTarget fieldName =>
        let qualifiedName := resolveQualifiedFieldName env types selectTarget fieldName
        let fieldType ← lookupFieldType qualifiedName
        let valTy := fieldType.getD (panic s!"could not find field type for {qualifiedName}")
        addFieldConstant qualifiedName valTy
        let readExpr := ⟨ .StaticCall "readField" [mkMd (.Identifier heapVar), selectTarget, mkMd (.Identifier qualifiedName)], md ⟩
        -- Unwrap Box: apply the appropriate destructor
        return mkMd <| .StaticCall (boxDestructorName valTy.val) [readExpr]
    | .StaticCall callee args =>
        let args' ← args.mapM (recurse env ·)
        let calleeReadsHeap ← readsHeap callee
        let calleeWritesHeap ← writesHeap callee
        if calleeWritesHeap then
          if valueUsed then
            let freshVar ← freshVarName
            let varDecl := mkMd (.LocalVariable freshVar ⟨.TInt, #[]⟩ none)
            let callWithHeap := ⟨ .Assign
              [mkMd (.Identifier heapVar), mkMd (.Identifier freshVar)]
              (⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), md ⟩), md ⟩
            return ⟨ .Block [varDecl, callWithHeap, mkMd (.Identifier freshVar)] none, md ⟩
          else
            return ⟨ .Assign [mkMd (.Identifier heapVar)] (⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), md ⟩), md ⟩
        else if calleeReadsHeap then
          return ⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), md ⟩
        else
          return ⟨ .StaticCall callee args', md ⟩
    | .InstanceCall callTarget callee args =>
        let t ← recurse env callTarget
        let args' ← args.mapM (recurse env ·)
        return ⟨ .InstanceCall t callee args', md ⟩
    | .IfThenElse c t e =>
        let e' ← match e with | some x => some <$> recurse env x valueUsed | none => pure none
        return ⟨ .IfThenElse (← recurse env c) (← recurse env t valueUsed) e', md ⟩
    | .Block stmts label =>
        let n := stmts.length
        let rec processStmts (env : TypeEnv) (idx : Nat) (remaining : List StmtExprMd) : TransformM (List StmtExprMd) := do
          match remaining with
          | [] => pure []
          | s :: rest =>
              let isLast := idx == n - 1
              -- Extend env for LocalVariable declarations
              let env' := match s.val with
                | .LocalVariable name ty _ => (name, ty) :: env
                | _ => env
              let s' ← recurse env s (isLast && valueUsed)
              let rest' ← processStmts env' (idx + 1) rest
              pure (s' :: rest')
          termination_by sizeOf remaining
        let stmts' ← processStmts env 0 stmts
        return ⟨ .Block stmts' label, md ⟩
    | .LocalVariable n ty i =>
        let i' ← match i with | some x => some <$> recurse env x | none => pure none
        return ⟨ .LocalVariable n ty i', md ⟩
    | .While c invs d b =>
        let invs' ← invs.mapM (recurse env ·)
        return ⟨ .While (← recurse env c) invs' d (← recurse env b false), md ⟩
    | .Return v =>
        let v' ← match v with | some x => some <$> recurse env x | none => pure none
        return ⟨ .Return v', md ⟩
    | .Assign targets v =>
        match targets with
        | [fieldSelectMd] =>
          match _h2 : fieldSelectMd.val with
          | .FieldSelect target fieldName =>
            let qualifiedName := resolveQualifiedFieldName env types target fieldName
            let fieldType ← lookupFieldType qualifiedName
            let valTy := fieldType.getD (panic s!"could not find field type for {qualifiedName}")
            addFieldConstant qualifiedName valTy
            let target' ← recurse env target
            let v' ← recurse env v
            -- Wrap value in Box constructor
            let boxedVal := mkMd <| .StaticCall (boxConstructorName valTy.val) [v']
            let heapAssign := ⟨ .Assign [mkMd (.Identifier heapVar)]
              (mkMd (.StaticCall "updateField" [mkMd (.Identifier heapVar), target', mkMd (.Identifier qualifiedName), boxedVal])), md ⟩
            if valueUsed then
              return ⟨ .Block [heapAssign, v'] none, md ⟩
            else
              return heapAssign
          | _ =>
            let tgt' ← recurse env fieldSelectMd
            return ⟨ .Assign [tgt'] (← recurse env v), md ⟩
        | [] =>
            return ⟨ .Assign [] (← recurse env v), md ⟩
        | tgt :: rest =>
            let tgt' ← recurse env tgt
            let targets' ← rest.mapM (recurse env ·)
            return ⟨ .Assign (tgt' :: targets') (← recurse env v), md ⟩
    | .PureFieldUpdate t f v => return ⟨ .PureFieldUpdate (← recurse env t) f (← recurse env v), md ⟩
    | .PrimitiveOp op args =>
      let args' ← args.mapM (recurse env ·)
      -- For == and != on Composite types, compare refs instead
      match op, args with
      | .Eq, [e1, _e2] =>
        let ty := (computeExprType env types e1).val
        match ty with
        | .UserDefined _ =>
          let ref1 := mkMd (.StaticCall "Composite..ref" [args'[0]!])
          let ref2 := mkMd (.StaticCall "Composite..ref" [args'[1]!])
          return ⟨ .PrimitiveOp .Eq [ref1, ref2], md ⟩
        | _ => return ⟨ .PrimitiveOp op args', md ⟩
      | .Neq, [e1, _e2] =>
        let ty := (computeExprType env types e1).val
        match ty with
        | .UserDefined _ =>
          let ref1 := mkMd (.StaticCall "Composite..ref" [args'[0]!])
          let ref2 := mkMd (.StaticCall "Composite..ref" [args'[1]!])
          return ⟨ .PrimitiveOp .Neq [ref1, ref2], md ⟩
        | _ => return ⟨ .PrimitiveOp op args', md ⟩
      | _, _ => return ⟨ .PrimitiveOp op args', md ⟩
    | .New _ => return expr
    | .ReferenceEquals l r => return ⟨ .ReferenceEquals (← recurse env l) (← recurse env r), md ⟩
    | .AsType t ty =>
        let t' ← recurse env t valueUsed
        let isCheck := ⟨ .IsType t' ty, md ⟩
        let assertStmt := ⟨ .Assert isCheck, md ⟩
        return ⟨ .Block [assertStmt, t'] none, md ⟩
    | .IsType t ty => return ⟨ .IsType (← recurse env t) ty, md ⟩
    | .Forall n ty b => return ⟨ .Forall n ty (← recurse env b), md ⟩
    | .Exists n ty b => return ⟨ .Exists n ty (← recurse env b), md ⟩
    | .Assigned n => return ⟨ .Assigned (← recurse env n), md ⟩
    | .Old v => return ⟨ .Old (← recurse env v), md ⟩
    | .Fresh v => return ⟨ .Fresh (← recurse env v), md ⟩
    | .Assert c => return ⟨ .Assert (← recurse env c), md ⟩
    | .Assume c => return ⟨ .Assume (← recurse env c), md ⟩
    | .ProveBy v p => return ⟨ .ProveBy (← recurse env v) (← recurse env p), md ⟩
    | .ContractOf ty f => return ⟨ .ContractOf ty (← recurse env f), md ⟩
    | _ => return expr
    termination_by sizeOf expr
    decreasing_by
      all_goals simp_wf
      all_goals
        have hval := WithMetadata.sizeOf_val_lt expr
        rw [_h] at hval; simp at hval
        first
          | term_by_mem
          | -- For the FieldSelect-inside-Assign case: target < fieldSelectMd < expr
            (have hfs := WithMetadata.sizeOf_val_lt fieldSelectMd; term_by_mem)

def heapTransformProcedure (proc : Procedure) : TransformM Procedure := do
  let heapName := "$heap"
  let heapInName := "$heap_in"
  let readsHeap := (← get).heapReaders.contains proc.name
  let writesHeap := (← get).heapWriters.contains proc.name

  -- Build the type environment from procedure parameters and constants
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type))

  if writesHeap then
    -- This procedure writes the heap - add $heap_in as input and $heap as output
    -- At the start, assign $heap_in to $heap, then use $heap throughout
    let heapInParam : Parameter := { name := heapInName, type := ⟨.THeap, #[]⟩ }
    let heapOutParam : Parameter := { name := heapName, type := ⟨.THeap, #[]⟩ }

    let inputs' := heapInParam :: proc.inputs
    let outputs' := heapOutParam :: proc.outputs

    -- Preconditions use $heap_in (the input state)
    let preconditions' ← proc.preconditions.mapM (heapTransformExpr heapInName initEnv)

    let bodyValueIsUsed := !proc.outputs.isEmpty
    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          -- First assign $heap_in to $heap, then transform body using $heap
          let assignHeap := mkMd (.Assign [mkMd (.Identifier heapName)] (mkMd (.Identifier heapInName)))
          let bodyExpr' ← heapTransformExpr heapName initEnv bodyExpr bodyValueIsUsed
          pure (.Transparent (mkMd (.Block [assignHeap, bodyExpr'] none)))
      | .Opaque postconds impl modif =>
          -- Postconditions use $heap (the output state)
          let postconds' ← postconds.mapM (heapTransformExpr heapName initEnv ·)
          let impl' ← match impl with
            | some implExpr =>
                let assignHeap := mkMd (.Assign [mkMd (.Identifier heapName)] (mkMd (.Identifier heapInName)))
                let implExpr' ← heapTransformExpr heapName initEnv implExpr bodyValueIsUsed
                pure (some (mkMd (.Block [assignHeap, implExpr'] none)))
            | none => pure none
          let modif' ← modif.mapM (heapTransformExpr heapName initEnv ·)
          pure (.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName initEnv ·)
          pure (.Abstract postconds')

    return { proc with
      inputs := inputs',
      outputs := outputs',
      preconditions := preconditions',
      body := body' }

  else if readsHeap then
    -- This procedure only reads the heap - add $heap as input only
    let heapParam : Parameter := { name := heapName, type := ⟨.THeap, #[]⟩ }
    let inputs' := heapParam :: proc.inputs

    let preconditions' ← proc.preconditions.mapM (heapTransformExpr heapName initEnv)

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformExpr heapName initEnv bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName initEnv ·)
          let impl' ← impl.mapM (heapTransformExpr heapName initEnv ·)
          let modif' ← modif.mapM (heapTransformExpr heapName initEnv ·)
          pure (.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName initEnv ·)
          pure (.Abstract postconds')

    return { proc with
      inputs := inputs',
      preconditions := preconditions',
      body := body' }

  else
    -- This procedure doesn't read or write the heap - no changes needed
    return proc

def heapParameterization (program : Program) : Program :=
  let heapReaders := computeReadsHeap program.staticProcedures
  let heapWriters := computeWritesHeap program.staticProcedures
  -- Extract field types from composite type definitions, qualified with composite type name
  let fieldTypes := program.types.foldl (fun acc typeDef =>
    match typeDef with
    | .Composite ct => acc ++ ct.fields.map (fun f => (ct.name ++ "." ++ f.name, f.type))
    | .Constrained _ => acc
    | .Datatype _ => acc) []
  let (procs', _) := (program.staticProcedures.mapM heapTransformProcedure).run
    { heapReaders, heapWriters, fieldTypes, types := program.types }
  -- Collect all qualified field names and generate a Field datatype
  let fieldNames := program.types.foldl (fun acc td =>
    match td with
    | .Composite ct => acc ++ ct.fields.map (fun f => ct.name ++ "." ++ f.name)
    | _ => acc) ([] : List Identifier)
  let fieldDatatype : TypeDefinition :=
    .Datatype { name := "Field", typeArgs := [], constructors := fieldNames.map fun n => { name := n, args := [] } }
  { program with
    staticProcedures := procs',
    types := program.types ++ [fieldDatatype] }

end Strata.Laurel
