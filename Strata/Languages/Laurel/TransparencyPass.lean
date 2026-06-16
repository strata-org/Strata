/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.CoreGroupingAndOrdering
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.DL.Lambda.TypeFactory

/-!
## Transparency Pass

For each Core procedure, generate a function with the same signature and name
suffixed with `$asFunction`. If a Core procedure is marked as transparent,
attempt to add a body to its function version. In the functional body,
assertions are erased and all calls are to functional versions. If the function
has a body, add a free postcondition to the related procedure that equates the
two.

This IR sits between Laurel and CoreWithLaurelTypes in the pipeline:
  Laurel → UnorderedCoreWithLaurelTypes → CoreWithLaurelTypes → Core
-/

namespace Strata.Laurel

public section

/-- Deep traversal that strips all Assert and Assume nodes from a StmtExpr tree.
    Assert/Assume nodes are replaced with `LiteralBool true`, and Block nodes
    are collapsed by filtering out trivial `LiteralBool true` leftovers. -/
def stripAssertAssume (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Assert _ | .Assume _ => ⟨.LiteralBool true, e.source⟩
    | .Block stmts label =>
      let stmts' := stmts.filter fun s =>
        match s.val with | .LiteralBool true => false | _ => true
      match stmts' with
      | [] => ⟨.LiteralBool true, e.source⟩
      | [s] => if label.isNone then s else ⟨.Block [s] label, e.source⟩
      | _ => ⟨.Block stmts' label, e.source⟩
    | _ => e) expr

/-- Adjust a datatype selector (destructor) name based on the `proof` flag.
    Destructor names contain `..` (e.g. `IntList..head`, `IntList..head!`).
    Tester names also contain `..` but start with `is` after the separator.
    - `proof = true` → use safe selectors (strip `!` suffix)
    - `proof = false` → use unsafe selectors (add `!` suffix) -/
private def adjustSelectorName (name : Identifier) : Identifier :=
  if Lambda.isTesterName name.text then name
  else if Lambda.isDestructorName name.text then
    -- Unsafe: add trailing "!" if not already present
    if name.text.endsWith Lambda.unsafeDestructorSuffix then name
    else { text := name.text ++ Lambda.unsafeDestructorSuffix, source := name.source }
  else name

/-- Rewrite StaticCall callees to their `$asFunction` versions,
    but only for procedures whose names appear in `nonExternalNames`. -/
private def rewriteCallsToFunctional (asFunctionNames : Std.HashSet String) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .StaticCall callee args =>
      if asFunctionNames.contains callee.text then
        let funcCallee := { callee with text := callee.text ++ "$asFunction", uniqueId := none }
        ⟨.StaticCall funcCallee args, e.source⟩
      else
        let newName := adjustSelectorName callee
        ⟨ .StaticCall newName args, e.source⟩
    | .PrimitiveOp operator arguments _ => ⟨ .PrimitiveOp operator arguments true, e.source⟩
    | _ => e) expr

/-- Rewrite quantifier bodies like function bodies: strip assert/assume and
    rewrite calls to their `$asFunction` variants. This ensures that calls
    inside quantifiers (e.g. in modifies frame conditions) reference the
    pure functional version and are not treated as imperative by later passes. -/
private def rewriteQuantifierBodies (nonExternalNames : Std.HashSet String) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Quantifier mode param trigger body =>
      let body' := rewriteCallsToFunctional nonExternalNames (stripAssertAssume body)
      let trigger' := trigger.map (rewriteCallsToFunctional nonExternalNames)
      ⟨.Quantifier mode param trigger' body', e.source⟩
    | _ => e) expr

/-- Apply quantifier body rewriting to all postconditions and the implementation
    of a procedure. -/
private def rewriteQuantifierBodiesInProc (nonExternalNames : Std.HashSet String) (proc : Procedure) : Procedure :=
  let rewrite := rewriteQuantifierBodies nonExternalNames
  match proc.body with
  | .Opaque postconds impl modif =>
    let postconds' := postconds.map fun c => { c with condition := rewrite c.condition }
    let impl' := impl.map rewrite
    { proc with body := .Opaque postconds' impl' modif }
  | .Transparent body =>
    { proc with body := .Transparent (rewrite body) }
  | .Abstract postconds =>
    let postconds' := postconds.map fun c => { c with condition := rewrite c.condition }
    { proc with body := .Abstract postconds' }
  | .External => proc

/-- Build a free postcondition equating the procedure's output to its functional version.
    For a procedure `foo(a, b) returns (r)`, produces:
      `r == foo$asFunction(a, b)` -/
private def mkFreePostcondition (proc : Procedure) : StmtExprMd :=
  let source := proc.name.source
  let funcName := { proc.name with text := proc.name.text ++ "$asFunction", uniqueId := none }
  let inputArgs := proc.inputs.map fun p => (⟨ .Var (.Local p.name), source ⟩ : StmtExprMd)
  let funcCall: StmtExprMd := ⟨ .StaticCall funcName inputArgs, source ⟩
  match proc.outputs with
  | [out] => ⟨ .PrimitiveOp .Eq [⟨ .Var (.Local out.name), source⟩, funcCall], source ⟩
  | _ => ⟨ .LiteralBool true, source ⟩

/-- Create the function copy of a procedure (suffixed `$asFunction`).
    If the procedure is transparent, include a functional body.
    Otherwise the function is opaque. -/
private def mkFunctionCopy (asFunctionNames : Std.HashSet String) (proc : Procedure) : Procedure :=
  let hasProcedureTwin := asFunctionNames.contains proc.name.text
  let funcName := if hasProcedureTwin then
    { proc.name with text := proc.name.text ++ "$asFunction", uniqueId := none }
    else proc.name
  let body := match proc.body with
    | .Transparent b => .Transparent (rewriteCallsToFunctional asFunctionNames (if hasProcedureTwin then stripAssertAssume b else b))
    | .Opaque _ _ _ => if hasProcedureTwin then .Opaque [] none [] else proc.body
    | x => x
  { proc with name := funcName, body := body }

/-- Append a free postcondition to a procedure's body postconditions.
    For Opaque and Abstract bodies, the free condition is appended to the
    existing postcondition list. For Transparent bodies, the body is promoted
    to Opaque so the free postcondition can be carried.
    This change in opaqueness is fine since the function copy now carries the transparent semantics. -/
private def addFreePostcondition (proc : Procedure) (freePost : StmtExprMd) : Procedure :=
  match freePost.val with
  | .LiteralBool true => proc  -- trivial, skip
  | _ =>
    let freeCond : Condition := { condition := freePost, free := true }
    match proc.body with
    | .Opaque postconds impl modif =>
      { proc with body := .Opaque (postconds ++ [freeCond]) impl modif }
    | .Abstract postconds =>
      { proc with body := .Abstract (postconds ++ [freeCond]) }
    | .Transparent body =>
      { proc with body := .Opaque [freeCond] (some body) [] }
    | _ => proc

/--
Transparency pass: translate a Laurel program to the UnorderedCoreWithLaurelTypes IR.

For each procedure:
- Generate a function with the same signature, named `foo$asFunction`
- If transparent, the function gets a functional body (assertions erased, calls to functional versions)
- If the function has a body, add a free postcondition equating the procedure output to the function
-/
def createFunctionsForTransparentBodies (program : Program) : UnorderedCoreWithLaurelTypes :=
  let (toUpdate, _) := program.staticProcedures.partition (fun p => !p.body.isExternal)
  let toUpdateNames : Std.HashSet String := toUpdate.foldl (fun s p => s.insert p.name.text) {}
  -- $asFunction copies for non-external procedures
  let functions := program.staticProcedures.map (mkFunctionCopy toUpdateNames)
  let coreProcedures := toUpdate.map fun proc =>
    let freePostcondition := mkFreePostcondition proc
    let proc := { proc with axioms := proc.axioms.map (rewriteCallsToFunctional toUpdateNames) }
    let proc := rewriteQuantifierBodiesInProc toUpdateNames proc
    addFreePostcondition proc freePostcondition
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  { functions, coreProcedures, datatypes, constants := program.constants }

public def transparencyPass : LaurelPass Laurel.Program UnorderedCoreWithLaurelTypes where
  name := "TransparencyPass"
  comesBefore := [⟨ orderingPass.meta, "Transparency pass creates functions that are not ordered" ⟩]
  documentation := "Translate a Laurel program to the UnorderedCoreWithLaurelTypes IR.
For each procedure:
  - Generate a function with the same signature, named `foo$asFunction`
  - If transparent, the function gets a functional body (assertions erased, calls to functional versions)
  - If the function has a body, add a free postcondition equating the procedure output to the function"
  run := fun p _ _ =>
    (createFunctionsForTransparentBodies p, [], {})

end -- public section
end Strata.Laurel
