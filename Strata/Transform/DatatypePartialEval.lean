/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions

namespace Strata

public section

/-! ## Datatype Partial Evaluation

Simplify tester and selector applications on known constructor terms:
- `tester(C(args))` → `true` if tester matches C, `false` otherwise
- `selector_i(C(args))` → `args[i]` if selector matches C

This is a pure Core-to-Core transform that reduces the number of
uninterpreted function applications downstream consumers need to handle.
-/

/-- Collected datatype metadata for partial evaluation. -/
structure DatatypeInfo where
  /-- Constructor name → its tester name -/
  constrToTester : Std.HashMap String String := {}
  /-- Tester name → the constructor it tests for -/
  testerToConstr : Std.HashMap String String := {}
  /-- All tester names for a given datatype (keyed by any constructor name) -/
  constrSiblingTesters : Std.HashMap String (List String) := {}
  /-- Selector name (e.g. "Any..as_int!") → (constructor name, field index) -/
  selectorInfo : Std.HashMap String (String × Nat) := {}
  /-- Set of all constructor names -/
  constrNames : Std.HashSet String := {}

/-- Build DatatypeInfo from a Core program's declarations. -/
def collectDatatypeInfo (pgm : Core.Program) : DatatypeInfo :=
  pgm.decls.foldl (init := {}) fun info decl =>
    match decl with
    | .type (.data dts) _ => dts.foldl (init := info) fun info dt =>
      let allTesters := dt.constrs.map (·.testerName)
      dt.constrs.foldl (init := info) fun info c =>
        let cname := c.name.name
        let selectors := (List.range c.args.length).foldl (init := info.selectorInfo) fun m i =>
          match c.args[i]? with
          | some (fieldId, _) =>
            let selName := s!"{dt.name}..{fieldId.name}!"
            m.insert selName (cname, i)
          | none => m
        { info with
          constrToTester := info.constrToTester.insert cname c.testerName
          testerToConstr := info.testerToConstr.insert c.testerName cname
          constrSiblingTesters := info.constrSiblingTesters.insert cname allTesters
          selectorInfo := selectors
          constrNames := info.constrNames.insert cname }
    | _ => info

/-- Decompose a constructor application: `C(a₁, ..., aₙ)` → `(C, [a₁,...,aₙ])`.
    Returns `none` if the head is not a known constructor.
    Does not check arity — partial applications return fewer arguments. -/
def matchConstrApp (dtInfo : DatatypeInfo) (e : Lambda.LExpr Core.CoreLParams.mono)
    : Option (String × List (Lambda.LExpr Core.CoreLParams.mono)) :=
  let rec collect (e : Lambda.LExpr Core.CoreLParams.mono)
      (args : List (Lambda.LExpr Core.CoreLParams.mono))
      : Lambda.LExpr Core.CoreLParams.mono × List (Lambda.LExpr Core.CoreLParams.mono) :=
    match e with
    | .app _ f a => collect f (a :: args)
    | other => (other, args)
  let (head, args) := collect e []
  match head with
  | .op _ o _ =>
    if dtInfo.constrNames.contains o.1 then some (o.1, args) else none
  | _ => none

/-- Try to simplify a unary application `op(arg)` where `arg` is already simplified.
    Returns `none` if no simplification applies. -/
def trySimplifyUnaryApp (dtInfo : DatatypeInfo)
    (appMd opMd : Core.ExpressionMetadata) (fn : Lambda.Identifier Core.CoreLParams.mono.base.IDMeta)
    (opTy : Option Core.CoreLParams.mono.TypeType)
    (arg' : Lambda.LExpr Core.CoreLParams.mono) : Option (Lambda.LExpr Core.CoreLParams.mono) :=
  let m : Core.ExpressionMetadata := default
  let fname := fn.1
  match dtInfo.testerToConstr.get? fname, matchConstrApp dtInfo arg' with
  | some expectedConstr, some (actualConstr, _) =>
    if actualConstr == expectedConstr then some (.const m (.boolConst true))
    else some (.const m (.boolConst false))
  | _, _ =>
  match dtInfo.selectorInfo.get? fname, matchConstrApp dtInfo arg' with
  | some (expectedConstr, fieldIdx), some (actualConstr, args) =>
    if actualConstr == expectedConstr then
      match args[fieldIdx]? with
      | some fieldVal => some fieldVal
      | none => none
    else none
  | _, _ => none

/-- Partially evaluate datatype tester and selector applications on known constructors.
- `tester(C(args))` → `true` if tester matches C, `false` otherwise
- `selector_i(C(args))` → `args[i]` if selector matches C
Recurses into subexpressions. -/
def partialEvalDatatypesCore (dtInfo : DatatypeInfo)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  match e with
  -- Unary application: tester(arg) or selector(arg)
  | .app appMd (.op opMd fn opTy) arg =>
    let arg' := partialEvalDatatypesCore dtInfo arg
    match trySimplifyUnaryApp dtInfo appMd opMd fn opTy arg' with
    | some result => result
    | none => .app appMd (.op opMd fn opTy) arg'
  -- Binary application: recurse into all subexpressions
  | .app m1 (.app m2 op l) r =>
    .app m1 (.app m2 (partialEvalDatatypesCore dtInfo op) (partialEvalDatatypesCore dtInfo l)) (partialEvalDatatypesCore dtInfo r)
  -- General application: recurse
  | .app m f a => .app m (partialEvalDatatypesCore dtInfo f) (partialEvalDatatypesCore dtInfo a)
  -- Quantifiers, ite: recurse into subexpressions
  | .quant m k name ty trigger body =>
    .quant m k name ty (partialEvalDatatypesCore dtInfo trigger) (partialEvalDatatypesCore dtInfo body)
  | .ite m c t e =>
    .ite m (partialEvalDatatypesCore dtInfo c) (partialEvalDatatypesCore dtInfo t) (partialEvalDatatypesCore dtInfo e)
  -- Leaves: unchanged
  | other => other

def partialEvalDatatypes (dtInfo : DatatypeInfo)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  partialEvalDatatypesCore dtInfo e

/-- Apply datatype partial evaluation to procedure bodies, specifications
    (pre/postconditions), and axioms in a Core program. -/
def partialEvalDatatypesInProgram (pgm : Core.Program) : Core.Program :=
  let dtInfo := collectDatatypeInfo pgm
  if dtInfo.constrNames.isEmpty then pgm
  else
    let pe := partialEvalDatatypes dtInfo
    let mapCmd : Core.Command → Core.Command
      | .cmd (.init n ty (.det e) md) => .cmd (.init n ty (.det (pe e)) md)
      | .cmd (.set n e md) => .cmd (.set n (e.map pe) md)
      | .cmd (.assert l e md) => .cmd (.assert l (pe e) md)
      | .cmd (.assume l e md) => .cmd (.assume l (pe e) md)
      | .cmd (.cover l e md) => .cmd (.cover l (pe e) md)
      | .call lhs pn args md => .call lhs pn (args.map pe) md
      | other => other
    let rec mapStmt : Core.Statement → Core.Statement
      | .cmd c => .cmd (mapCmd c)
      | .block l b md => .block l (b.map mapStmt) md
      | .ite c t e md => .ite (c.map pe) (t.map mapStmt) (e.map mapStmt) md
      | .loop g m invs b md => .loop (g.map pe) (m.map pe) (invs.map pe) (b.map mapStmt) md
      | .exit l md => .exit l md
      | .funcDecl d md => .funcDecl d md
      | .typeDecl tc md => .typeDecl tc md
    let mapCheck (c : Core.Procedure.Check) : Core.Procedure.Check :=
      { c with expr := pe c.expr }
    let decls' := pgm.decls.map fun d =>
      match d with
      | .ax ax md => .ax { ax with e := pe ax.e } md
      | .proc p md =>
        let spec' := { p.spec with
          preconditions := p.spec.preconditions.map (fun (l, c) => (l, mapCheck c))
          postconditions := p.spec.postconditions.map (fun (l, c) => (l, mapCheck c))
        }
        .proc { p with spec := spec', body := p.body.map mapStmt } md
      | other => other
    { pgm with decls := decls' }

end -- public section

end Strata
