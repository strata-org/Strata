/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Core.Factory
import Strata.Util.Tactics

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
private def collectHighTypeNames (ty : HighTypeMd) : CollectM Unit := do
  match _h : ty.val with
  | .UserDefined name => addTypeName name.text
  -- A type variable references no prelude type name.
  | .TVar _ => pure ()
  | .TCore _ => pure ()
  | .TSet et => collectHighTypeNames et
  | .TMap kt vt => collectHighTypeNames kt; collectHighTypeNames vt
  | .Applied base args =>
    collectHighTypeNames base; args.attach.forM (fun ⟨a, _⟩ => collectHighTypeNames a)
  | .Pure base => collectHighTypeNames base
  | .Intersection types => types.attach.forM (fun ⟨t, _⟩ => collectHighTypeNames t)
  | .TVoid | .TBool | .TInt | .TFloat64 | .TReal | .TString
  | .TBv _ | .Unknown | .MultiValuedExpr _ => pure ()
  termination_by ty
  decreasing_by ast_recursion_decreasing

/-- Collect all referenced names (procedure calls, type references) from a StmtExpr tree. -/
private def collectExprNames (expr : StmtExprMd) : CollectM Unit := do
  match _h : expr.val with
  | .StaticCall callee args =>
    addProcName callee.text; args.attach.forM (fun ⟨a, _⟩ => collectExprNames a)
  | .New ref typeArgs => addTypeName ref.text; typeArgs.forM collectHighTypeNames
  | .InstanceCall target callee args =>
    addProcName callee.text; collectExprNames target; args.attach.forM (fun ⟨a, _⟩ => collectExprNames a)
  | .IfThenElse cond thenB elseB =>
    collectExprNames cond; collectExprNames thenB
    elseB.attach.forM (fun ⟨e, _⟩ => collectExprNames e)
  | .Block stmts _ => stmts.attach.forM (fun ⟨s, _⟩ => collectExprNames s)
  | .While cond invs dec body _ =>
    collectExprNames cond; invs.attach.forM (fun ⟨i, _⟩ => collectExprNames i)
    dec.attach.forM (fun ⟨d, _⟩ => collectExprNames d)
    collectExprNames body
  | .Assign targets value =>
    collectExprNames value
    for ⟨t, _⟩ in targets.attach do
      match _htv : t.val with
      | .Field target _ => collectExprNames target
      | .Local _ => pure ()
      | .Declare param => collectHighTypeNames param.type
  | .IncrDecr _ _ target =>
    match _hit : target.val with
    | .Field tgt _ => collectExprNames tgt
    | .Local _ => pure ()
    | .Declare param => collectHighTypeNames param.type
  | .Var (.Field target _) => collectExprNames target
  | .Var (.Declare param) => collectHighTypeNames param.type
  | .PureFieldUpdate target _ newVal =>
    collectExprNames target; collectExprNames newVal
  | .PrimitiveOp _ args _ => args.attach.forM (fun ⟨a, _⟩ => collectExprNames a)
  | .AsType target ty => collectExprNames target; collectHighTypeNames ty
  | .IsType target ty => collectExprNames target; collectHighTypeNames ty
  | .Quantifier _ param trigger body =>
    collectHighTypeNames param.type
    trigger.attach.forM (fun ⟨t, _⟩ => collectExprNames t)
    collectExprNames body
  | .Assert cond => collectExprNames cond.condition
  | .Assume cond => collectExprNames cond
  | .Return val => val.attach.forM (fun ⟨v, _⟩ => collectExprNames v)
  | .Old val | .Fresh val | .Assigned val => collectExprNames val
  | .ProveBy val proof => collectExprNames val; collectExprNames proof
  | .ContractOf _ func => collectExprNames func
  | .ReferenceEquals lhs rhs => collectExprNames lhs; collectExprNames rhs
  | .Hole _ ty => ty.forM collectHighTypeNames
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
  | .Var (.Local _) | .This | .Abstract | .All => pure ()
  termination_by expr
  decreasing_by
    all_goals simp_wf
    all_goals (try have := AstNode.sizeOf_val_lt expr)
    all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
    all_goals (try term_by_mem)
    -- `.IncrDecr` field-target: sizeOf tgt < sizeOf target (Field lemma) < sizeOf expr.
    all_goals (try (have := Variable.sizeOf_field_target_lt_of_eq _hit
                    cases expr; simp_all; omega))
    -- `.Assign` field-target (attach loop): sizeOf target < sizeOf t (Field lemma) <
    -- sizeOf targets (list mem) < sizeOf expr.
    all_goals (try (have := Variable.sizeOf_field_target_lt_of_eq _htv
                    have := List.sizeOf_lt_of_mem ‹_ ∈ _›
                    cases expr; simp_all; omega))
    all_goals (cases expr; simp_all; omega)

/-- Collect names from a procedure body. -/
private def collectBodyNames (body : Body) : CollectM Unit := do
  match body with
  | .Transparent expr => collectExprNames expr
  | .Opaque posts impl modifies =>
    posts.forM (collectExprNames ·.condition)
    impl.forM collectExprNames
    modifies.forM collectExprNames
  | .Abstract posts => posts.forM (collectExprNames ·.condition)
  | .External => pure ()

/-- Collect all names referenced by a procedure (signature + body). -/
private def collectProcDeps (proc : Procedure) : CollectM Unit := do
  proc.inputs.forM  fun p => collectHighTypeNames p.type
  proc.outputs.forM fun p => collectHighTypeNames p.type
  proc.preconditions.forM (collectExprNames ·.condition)
  proc.decreases.forM collectExprNames
  proc.invokeOn.forM collectExprNames
  collectBodyNames proc.body

/-- Collect all names referenced by a type definition. -/
private def collectTypeDefDeps (td : TypeDefinition) : CollectM Unit := do
  match td with
  | .Composite ct =>
    ct.fields.forM fun f => collectHighTypeNames f.type
    -- `extending` is `List HighTypeMd`; prelude dep-collection needs the FULL type
    -- (both the parent base AND any concrete arg, e.g. `Base<int>` → Base AND int),
    -- so recurse via `collectHighTypeNames` rather than peeling to the base name.
    ct.extending.forM collectHighTypeNames
    ct.instanceProcedures.forM collectProcDeps
  | .Constrained ct =>
    collectHighTypeNames ct.base
    collectExprNames ct.constraint
    collectExprNames ct.witness
  | .Datatype dt =>
    for c in dt.constructors do
      c.args.forM fun arg => collectHighTypeNames arg.type
  | .Alias ta =>
    collectHighTypeNames ta.target

/-- Run a CollectM action and return the collected state. -/
private def runCollect (action : CollectM Unit) : CollectState :=
  (action.run {}).snd

/-- Merge procNames and typeNames into a single set. -/
private def CollectState.allNames (s : CollectState) : Std.HashSet String :=
  s.typeNames.fold (init := s.procNames) fun acc n => acc.insert n

/-- Collect StaticCall targets from an invokeOn expression.
    invokeOn expressions are expected to be simple `StaticCall` trees
    like `f(g(x))` with `Identifier` or literal leaves.  Returns an
    error if an unexpected node is encountered. -/
private def collectInvokeOnTargets (expr : StmtExprMd)
    : Except String (List String) := do
  match _h : expr.val with
  | .StaticCall callee args =>
    let rest ← args.attach.flatMapM (fun ⟨a, _⟩ => collectInvokeOnTargets a)
    return callee.text :: rest
  | .Var (.Local _) | .LiteralInt _ | .LiteralBool _ | .LiteralString _
  | .LiteralDecimal _ | .LiteralBv _ _ => return []
  | _ =>
    throw s!"FilterPrelude.collectInvokeOnTargets: unexpected node in invokeOn expression"
  termination_by expr
  decreasing_by ast_recursion_decreasing

/-- Monad for building the dependency map with duplicate-name detection. -/
private abbrev DepM := StateT (Std.HashMap String (Std.HashSet String)) (Except String)

/-- Insert a new binding, failing if the name is already bound. -/
private def insertNew (key : String) (deps : Std.HashSet String) (context : String)
    : DepM Unit := do
  let m ← get
  if key ∈ m then
    throw s!"FilterPrelude.buildDependencyMap: duplicate name '{key}' ({context})"
  set (m.insert key deps)

/-- Build a dependency map: declaration name → set of names it references.
    For datatypes, also maps constructor, destructor, and tester names
    to the same dependencies (plus the parent type).
    For procedures with `invokeOn`, adds reverse dependencies so that
    needing the invoked function also pulls in the axiom procedure.
    Returns `Except.error` if two declarations bind the same name. -/
private def buildDependencyMap (prog : Laurel.Program)
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
        let targets ← collectInvokeOnTargets invokeExpr
        modify fun m =>
          targets.foldl (init := m) fun m target =>
            m.alter target fun me => me.getD {} |>.insert proc.name.text
  let ((), m) ← action.run {}
  return m

/-- Compute names reachable from seeds via the dependency map (BFS). -/
private partial def reachableNamesAux
    (depMap : Std.HashMap String (Std.HashSet String))
    (worklist : List String) (visited : Std.HashSet String) : Std.HashSet String :=
  match worklist with
  | [] => visited
  | name :: rest =>
    if name ∈ visited then
      reachableNamesAux depMap rest visited
    else
      let visited := visited.insert name
      match depMap[name]? with
      | some deps =>
        let newWork := deps.fold (init := rest) fun acc dep =>
          if dep ∈ visited then acc else dep :: acc
        reachableNamesAux depMap newWork visited
      | none => reachableNamesAux depMap rest visited

/-- Collect all names referenced by a user Laurel program. -/
private def collectProgramRefs (prog : Laurel.Program) : CollectState :=
  runCollect do
    prog.staticProcedures.forM collectProcDeps
    prog.types.forM collectTypeDefDeps

/-- Filter a prelude Laurel program to only include declarations
    transitively needed by the user program. -/
public def filterPrelude (prelude user : Laurel.Program)
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
    staticProcedures := prelude.staticProcedures.filter fun p => p.name.text ∈ needed
    types := prelude.types.filter fun td => td.name.text ∈ needed
  }

end Strata.Laurel
