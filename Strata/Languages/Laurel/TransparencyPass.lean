/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

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

/--
An intermediate representation produced by the transparency pass.
Functions are pure computational procedures (suffixed `$asFunction`);
coreProcedures are the original procedures with any free postconditions
embedded in their `Body.Opaque` postcondition lists.
-/
public structure UnorderedCoreWithLaurelTypes where
  functions : List Procedure
  coreProcedures : List Procedure
  datatypes : List DatatypeDefinition
  constants : List Constant

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
  -- Only adjust destructor names (contain ".." but are not testers)
  match name.text.splitOn ".." with
  | [_, suffix] =>
    if suffix.startsWith "is" then name  -- tester, leave unchanged
    else
      -- Unsafe: add trailing "!" if not already present
      if name.text.endsWith "!" then name else { text := name.text ++ "!", source := name.source }
  | _ => name  -- not a destructor name, leave unchanged

/-- Rewrite StaticCall callees to their `$asFunction` versions,
    but only for procedures whose names appear in `nonExternalNames`. -/
private def rewriteCallsToFunctional (asFunctionNames : List String) (expr : StmtExprMd) : StmtExprMd :=
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
private def mkFunctionCopy (asFunctionNames : List String) (proc : Procedure) : Procedure :=
  let funcName := { proc.name with text := proc.name.text ++ "$asFunction", uniqueId := none }
  let body := match proc.body with
    | .Transparent b => .Transparent (rewriteCallsToFunctional asFunctionNames (stripAssertAssume b))
    | .Opaque _ _ _ => .Opaque [] none []
    | x => x
  { proc with name := funcName, isFunctional := true, body := body, preconditions := [] }

/-- Check whether a function copy has a body (i.e. the procedure was transparent). -/
private def functionHasBody (proc : Procedure) : Bool :=
  match proc.body with
  | .Transparent _ => true
  | _ => false

/-- Append a free postcondition to a procedure's body postconditions.
    For Opaque and Abstract bodies, the free condition is appended to the
    existing postcondition list. For Transparent bodies, the body is promoted
    to Opaque so the free postcondition can be carried. -/
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
def transparencyPass (program : Program) : UnorderedCoreWithLaurelTypes :=
  let (skipped, notSkipped) := program.staticProcedures.partition (fun p => p.body.isExternal ||
    -- Skip functions until we introduce a contract pass,
    -- which enables lifting procedure calls from contracts
    p.isFunctional)
  let asFunctionNames := notSkipped.map (fun p => p.name.text)
  let asFunctions := notSkipped.map (mkFunctionCopy asFunctionNames)

  -- External procedures get a plain function copy (they have no $asFunction version)
  let (skippedFunctions, skippedProcedures) := skipped.partition (fun p => p.isFunctional)
  let functions := skippedFunctions ++ asFunctions
  let coreProcedures := notSkipped.map fun p =>
    let freePostcondition := mkFreePostcondition p
    let p := addFreePostcondition p freePostcondition
    { p with isFunctional := false }
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  let procs: List Procedure := skippedProcedures ++ coreProcedures
  { functions, coreProcedures := procs, datatypes, constants := program.constants }

open Std (Format ToFormat)

def formatUnorderedCoreWithLaurelTypes (p : UnorderedCoreWithLaurelTypes) : Format :=
  let datatypeFmts := p.datatypes.map ToFormat.format
  let constantFmts := p.constants.map ToFormat.format
  let functionFmts := p.functions.map ToFormat.format
  let procFmts := p.coreProcedures.map ToFormat.format
  Format.joinSep (datatypeFmts ++ constantFmts ++ functionFmts ++ procFmts) "\n\n"

instance : ToFormat UnorderedCoreWithLaurelTypes where
  format := formatUnorderedCoreWithLaurelTypes

end -- public section
end Strata.Laurel
