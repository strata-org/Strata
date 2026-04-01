/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-! ### Prelude Filtering

Restrict the Laurel prelude to only the `staticProcedures` and `types`
transitively needed by the user program, reducing the Core program size
for SMT verification.

#### Name collection

We collect two categories of names from the user program:

- **procNames**: targets of `StaticCall` and `InstanceCall`. In practice
  this includes true procedure calls (e.g. `print`, `Any_get`) as well as
  datatype constructor calls (`NoError`, `from_string`), testers (`isError`),
  and destructors (`Any..as_string!`), since the Laurel IR uses `StaticCall`
  as the uniform calling convention for all of these.

- **typeNames**: references from `UserDefined` types, `New` expressions,
  and composite type `extending` clauses.

#### Dependency map and datatype aliases

The dependency map keys each prelude declaration by its canonical name.
For datatypes, we also create alias entries so that constructor, tester,
and destructor names resolve back to the parent type:

- Constructor `c` of datatype `D`: key `c.name` → deps of `D` ∪ {`D`}
- Tester: key `"D..is" ++ c.name` → deps of `D` ∪ {`D`}
- Destructor: key `"D..field"` → deps of `D` ∪ {`D`}
- Bang destructor: key `"D..field!"` → deps of `D` ∪ {`D`}

This ensures that e.g. a `StaticCall "NoError"` in the user program
transitively pulls in the `Error` datatype and all its dependencies.

#### Reachability

Starting from the collected user names, we compute a BFS transitive
closure over the dependency map to find all needed declarations, then
filter the prelude's `staticProcedures` and `types` to that set. -/

namespace Strata.Laurel

open Laurel

/-- State for name collection, distinguishing procedure names from type names. -/
structure CollectState where
  /-- Names from StaticCall, InstanceCall targets. -/
  procNames : Std.HashSet String := {}
  /-- Names from UserDefined types, New, extending. -/
  typeNames : Std.HashSet String := {}

abbrev CollectM := StateM CollectState

private def addProcName (name : String) : CollectM Unit :=
  modify fun s => { s with procNames := s.procNames.insert name }

private def addTypeName (name : String) : CollectM Unit :=
  modify fun s => { s with typeNames := s.typeNames.insert name }

/-- Collect type names referenced in a HighType. -/
private partial def collectHighTypeNames (ty : HighTypeMd) : CollectM Unit := do
  match ty.val with
  | .UserDefined name => addTypeName name.text
  | .TCore _ => pure ()
  | .TTypedField vt => collectHighTypeNames vt
  | .TSet et => collectHighTypeNames et
  | .TMap kt vt => collectHighTypeNames kt; collectHighTypeNames vt
  | .Applied base args =>
    collectHighTypeNames base; args.forM collectHighTypeNames
  | .Pure base => collectHighTypeNames base
  | .Intersection types => types.forM collectHighTypeNames
  | .TVoid | .TBool | .TInt | .TFloat64 | .TReal | .TString | .THeap
  | .Unknown => pure ()

/-- Collect all referenced names (procedure calls, type references) from a StmtExpr tree. -/
private partial def collectExprNames (expr : StmtExprMd) : CollectM Unit := do
  match expr.val with
  | .StaticCall callee args =>
    addProcName callee.text; args.forM collectExprNames
  | .New ref => addTypeName ref.text
  | .InstanceCall target callee args =>
    addProcName callee.text; collectExprNames target; args.forM collectExprNames
  | .IfThenElse cond thenB elseB =>
    collectExprNames cond; collectExprNames thenB
    match elseB with | some e => collectExprNames e | none => pure ()
  | .Block stmts _ => stmts.forM collectExprNames
  | .LocalVariable _ ty init =>
    collectHighTypeNames ty
    match init with | some e => collectExprNames e | none => pure ()
  | .While cond invs dec body =>
    collectExprNames cond; invs.forM collectExprNames
    match dec with | some d => collectExprNames d | none => pure ()
    collectExprNames body
  | .Assign targets value =>
    collectExprNames value; targets.forM collectExprNames
  | .FieldSelect target _ => collectExprNames target
  | .PureFieldUpdate target _ newVal =>
    collectExprNames target; collectExprNames newVal
  | .PrimitiveOp _ args => args.forM collectExprNames
  | .AsType target ty => collectExprNames target; collectHighTypeNames ty
  | .IsType target ty => collectExprNames target; collectHighTypeNames ty
  | .Forall param trigger body =>
    collectHighTypeNames param.type
    match trigger with | some t => collectExprNames t | none => pure ()
    collectExprNames body
  | .Exists param trigger body =>
    collectHighTypeNames param.type
    match trigger with | some t => collectExprNames t | none => pure ()
    collectExprNames body
  | .Assert cond | .Assume cond => collectExprNames cond
  | .Return val => match val with | some v => collectExprNames v | none => pure ()
  | .Old val | .Fresh val | .Assigned val => collectExprNames val
  | .ProveBy val proof => collectExprNames val; collectExprNames proof
  | .ContractOf _ func => collectExprNames func
  | .ReferenceEquals lhs rhs => collectExprNames lhs; collectExprNames rhs
  | .Hole _ ty => match ty with | some t => collectHighTypeNames t | none => pure ()
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Identifier _ | .This | .Abstract | .All => pure ()

/-- Collect names from a procedure body. -/
private partial def collectBodyNames (body : Body) : CollectM Unit := do
  match body with
  | .Transparent expr => collectExprNames expr
  | .Opaque posts impl modifies =>
    posts.forM collectExprNames
    match impl with | some i => collectExprNames i | none => pure ()
    modifies.forM collectExprNames
  | .Abstract posts => posts.forM collectExprNames
  | .External => pure ()

/-- Collect all names referenced by a procedure (signature + body). -/
private partial def collectProcDeps (proc : Procedure) : CollectM Unit := do
  proc.inputs.forM  fun p => collectHighTypeNames p.type
  proc.outputs.forM fun p => collectHighTypeNames p.type
  proc.preconditions.forM collectExprNames
  match proc.decreases with | some d => collectExprNames d | none => pure ()
  match proc.invokeOn with | some t => collectExprNames t | none => pure ()
  match proc.determinism with
  | .deterministic mreads => mreads.mapM collectExprNames
  | .nondeterministic => pure ()
  collectBodyNames proc.body

/-- Collect all names referenced by a type definition. -/
private partial def collectTypeDefDeps (td : TypeDefinition) : CollectM Unit := do
  match td with
  | .Composite ct =>
    ct.fields.forM fun f => collectHighTypeNames f.type
    for e in ct.extending do addTypeName e.text
    ct.instanceProcedures.forM collectProcDeps
  | .Constrained ct =>
    collectHighTypeNames ct.base
    collectExprNames ct.constraint
    collectExprNames ct.witness
  | .Datatype dt =>
    for c in dt.constructors do
      c.args.forM fun arg => collectHighTypeNames arg.type

/-- Run a CollectM action and return the collected state. -/
private def runCollect (action : CollectM Unit) : CollectState :=
  (action.run {}).snd

/-- Merge procNames and typeNames into a single set. -/
private def CollectState.allNames (s : CollectState) : Std.HashSet String :=
  s.typeNames.fold (init := s.procNames) fun acc n => acc.insert n

/-- Collect StaticCall targets from an expression (top-level only). -/
private partial def collectInvokeOnTargets (expr : StmtExprMd) : List String :=
  match expr.val with
  | .StaticCall callee args =>
    callee.text :: args.flatMap collectInvokeOnTargets
  | _ => []

/-- Monad for building the dependency map with duplicate-name detection. -/
private abbrev DepM := StateT (Std.HashMap String (Std.HashSet String)) (Except String)

/-- Insert a new binding, failing if the name is already bound. -/
private def insertNew (key : String) (deps : Std.HashSet String) (context : String)
    : DepM Unit := do
  let m ← get
  if m.contains key then
    throw s!"FilterPrelude.buildDependencyMap: duplicate name '{key}' ({context})"
  set (m.insert key deps)

/-- Build a dependency map: declaration name → set of names it references.
    For datatypes, also maps constructor, destructor, and tester names
    to the same dependencies (plus the parent type).
    For procedures with `invokeOn`, adds reverse dependencies so that
    needing the invoked function also pulls in the axiom procedure.
    Returns `Except.error` if two declarations bind the same name. -/
private partial def buildDependencyMap (prog : Laurel.Program)
    : Except String (Std.HashMap String (Std.HashSet String)) := do
  let action : DepM Unit := do
    for proc in prog.staticProcedures do
      insertNew proc.name.text (runCollect (collectProcDeps proc)).allNames
        s!"procedure '{proc.name.text}'"
    for td in prog.types do
      let name := td.name.text
      let deps := (runCollect (collectTypeDefDeps td)).allNames
      insertNew name deps s!"type '{name}'"
      if let .Datatype dt := td then
        for c in dt.constructors do
          insertNew c.name.text (deps.insert name)
            s!"constructor '{c.name.text}' of datatype '{name}'"
          insertNew (dt.testerName c) (deps.insert name)
            s!"tester '{dt.testerName c}' of datatype '{name}'"
          for a in c.args do
            insertNew (dt.destructorName a) (deps.insert name)
              s!"destructor '{dt.destructorName a}'"
            insertNew (dt.unsafeDestructorName a) (deps.insert name)
              s!"destructor '{dt.unsafeDestructorName a}'"
    -- Reverse invokeOn dependencies: if proc P has `invokeOn f(...)`,
    -- then needing f should also pull in P.
    -- These augment existing entries, so we merge rather than insertNew.
    for proc in prog.staticProcedures do
      if let some invokeExpr := proc.invokeOn then
        for target in collectInvokeOnTargets invokeExpr do
          let m ← get
          let existing := m[target]?.getD {}
          set (m.insert target (existing.insert proc.name.text))
  let ((), m) ← action.run {}
  return m

/-- Compute names reachable from seeds via the dependency map (BFS). -/
private partial def reachableNamesAux
    (depMap : Std.HashMap String (Std.HashSet String))
    (worklist : List String) (visited : Std.HashSet String) : Std.HashSet String :=
  match worklist with
  | [] => visited
  | name :: rest =>
    if visited.contains name then reachableNamesAux depMap rest visited
    else
      let visited := visited.insert name
      match depMap[name]? with
      | some deps =>
        let newWork := deps.fold (init := rest) fun acc dep =>
          if visited.contains dep then acc else dep :: acc
        reachableNamesAux depMap newWork visited
      | none => reachableNamesAux depMap rest visited

/-- Collect all names referenced by a user Laurel program. -/
private partial def collectProgramRefs (prog : Laurel.Program) : CollectState :=
  runCollect do
    prog.staticProcedures.forM collectProcDeps
    prog.types.forM collectTypeDefDeps

/-- Filter a prelude Laurel program to only include declarations
    transitively needed by the user program. -/
public partial def filterPrelude (prelude user : Laurel.Program)
    : Except String Laurel.Program := do
  -- Guard: filterPrelude does not yet track dependencies through static fields
  -- or constants.  Error early if either program contains them so a silent
  -- under-filtering cannot occur.
  unless prelude.staticFields.isEmpty do
    throw "FilterPrelude: prelude contains static fields, which are not yet supported"
  unless prelude.constants.isEmpty do
    throw "FilterPrelude: prelude contains constants, which are not yet supported"
  unless user.staticFields.isEmpty do
    throw "FilterPrelude: user program contains static fields, which are not yet supported"
  unless user.constants.isEmpty do
    throw "FilterPrelude: user program contains constants, which are not yet supported"
  let refs := collectProgramRefs user
  let depMap ← buildDependencyMap prelude
  let seeds := refs.allNames.fold (init := []) fun acc s => s :: acc
  let needed := reachableNamesAux depMap seeds {}
  return { prelude with
    staticProcedures := prelude.staticProcedures.filter fun p =>
      needed.contains p.name.text
    types := prelude.types.filter fun td =>
      needed.contains td.name.text }

end Strata.Laurel
