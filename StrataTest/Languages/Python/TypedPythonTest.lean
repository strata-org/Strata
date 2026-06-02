/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.Specs.DDM

/-! # `--typed-python` Spec-Layer Tests

End-to-end coverage of the user-code lowering lives in the
`tests/test_typed_python_*.py` snapshot pairs. This file unit-tests
the spec-layer pieces those snapshots can't easily inspect: native
  lowering of primitives and containers, refusal of unsupported types,
  and emission of preconditions/postconditions in their native form.
-/

namespace Strata.Python.TypedPythonTest

open Strata.Python.Specs
open Strata.Laurel (Procedure formatProcedure)

private def loc : SourceRange := default

private def identType (nm : PythonIdent) : SpecType := SpecType.ident loc nm

private def listOf (inner : PythonIdent) : SpecType :=
  SpecType.ident loc .typingList #[identType inner]

private def dictOf (k v : PythonIdent) : SpecType :=
  SpecType.ident loc .typingDict #[identType k, identType v]

private def mkArg (name : String) (type : SpecType) : Specs.Arg :=
  { name, type }

private def mkFunc (name : String) (args : Array Specs.Arg) (ret : SpecType)
    (preconds : Array Specs.Assertion := #[]) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name
    args := { args, kwonly := #[] }
    returnType := ret
    isOverload := false
    preconditions := preconds, postconditions := #[]
  }

private def assertionOf (formula : SpecExpr) : Specs.Assertion :=
  { message := #[], formula }

private def testModule : String := "t"
private def prefix_ : String := testModule ++ "_"

/-- Build the Laurel program from a list of pyspec signatures. -/
private def buildSpecs (sigs : Array Signature) (typedPython : Bool)
    : IO Strata.PySpecLaurelResult := do
  IO.FS.withTempDir fun dir => do
    let ionFile := dir / "test.pyspec.ion"
    writeDDM ionFile sigs
    let some mod := Python.ModuleName.ofString? testModule
      | throw <| IO.userError "ModuleName parse failed"
    let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
    let result ←
      Strata.buildPySpecLaurel pctx #[(mod, ionFile.toString)] {}
        (typedPython := typedPython) |>.toBaseIO
    match result with
    | .ok r => pure r
    | .error _ =>
      let msgs ← pctx.getMessages
      throw <| IO.userError <| String.intercalate "\n" <|
        msgs.toList.map fun m => s!"{m.kind.category}: {m.message}"

/-- Run typed-python lowering and expect a refusal; return the joined
    pipeline messages (`category: message` per line). -/
private def expectRefusal (sigs : Array Signature) : IO String :=
  IO.FS.withTempDir fun dir => do
    let ionFile := dir / "test.pyspec.ion"
    writeDDM ionFile sigs
    let some mod := Python.ModuleName.ofString? testModule
      | throw <| IO.userError "ModuleName parse failed"
    let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
    let result ←
      Strata.buildPySpecLaurel pctx #[(mod, ionFile.toString)] {}
        (typedPython := true) |>.toBaseIO
    match result with
    | .ok _ => throw <| IO.userError "expected refusal, got success"
    | .error _ =>
      let msgs ← pctx.getMessages
      pure <| String.intercalate "\n" <|
        msgs.toList.map fun m => s!"{m.kind.category}: {m.message}"

/-- Find a procedure by source-level name (the lowering prefixes the
    module name). -/
private def findProc (result : Strata.PySpecLaurelResult) (name : String)
    : IO Procedure := do
  let target := prefix_ ++ name
  match result.laurelProgram.staticProcedures.find? (·.name.text == target) with
  | some p => pure p
  | none => throw <| IO.userError s!"{name} not found"

/-- Short tag for a `HighType`'s outermost constructor. -/
private partial def shape : Strata.Laurel.HighType → String
  | .TInt => "Int"
  | .TBool => "Bool"
  | .TReal => "Real"
  | .TString => "String"
  | .TSeq inner => s!"TSeq ({shape inner.val})"
  | .TMap k v => s!"TMap ({shape k.val}) ({shape v.val})"
  | .UserDefined nm => s!"UserDefined({nm.text})"
  | .TCore "Any" => "Any"
  | .TCore s => s!"TCore({s})"
  | _ => "Other"

/-! ## Pyspec native lowering -/

-- Primitives lower to native sorts under `--typed-python`.
/-- info: Int / Bool / String / Real -/
#guard_msgs in
#eval do
  let result ← buildSpecs #[
    mkFunc "scalars"
      #[mkArg "a" (identType .builtinsInt),
        mkArg "b" (identType .builtinsBool),
        mkArg "c" (identType .builtinsStr),
        mkArg "d" (identType .builtinsFloat)]
      (identType .builtinsInt)
  ] (typedPython := true)
  let proc ← findProc result "scalars"
  let names := proc.inputs.map (fun (p : Strata.Laurel.Parameter) => shape p.type.val)
  IO.println (String.intercalate " / " names)

-- Default mode keeps every primitive as `Any` (UserDefined sentinel).
/-- info: UserDefined(Any) / UserDefined(Any) / UserDefined(Any) / UserDefined(Any) -/
#guard_msgs in
#eval do
  let result ← buildSpecs #[
    mkFunc "scalars"
      #[mkArg "a" (identType .builtinsInt),
        mkArg "b" (identType .builtinsBool),
        mkArg "c" (identType .builtinsStr),
        mkArg "d" (identType .builtinsFloat)]
      (identType .noneType)
  ] (typedPython := false)
  let proc ← findProc result "scalars"
  let names := proc.inputs.map (fun (p : Strata.Laurel.Parameter) => shape p.type.val)
  IO.println (String.intercalate " / " names)

-- `list[int]` and `dict[str, int]` lower to typed containers.
/-- info: TSeq (Int) / TMap (String) (Int) -/
#guard_msgs in
#eval do
  let result ← buildSpecs #[
    mkFunc "containers"
      #[mkArg "xs" (listOf .builtinsInt),
        mkArg "m" (dictOf .builtinsStr .builtinsInt)]
      (identType .builtinsInt)
  ] (typedPython := true)
  let proc ← findProc result "containers"
  let parts := proc.inputs.map (fun (p : Strata.Laurel.Parameter) => shape p.type.val)
  IO.println (String.intercalate " / " parts)

-- Nested `list[list[int]]` recurses through `specTypeToNative`.
/-- info: TSeq (TSeq (Int)) -/
#guard_msgs in
#eval do
  let result ← buildSpecs #[
    mkFunc "matrix"
      #[mkArg "m" (SpecType.ident loc .typingList #[listOf .builtinsInt])]
      (identType .builtinsInt)
  ] (typedPython := true)
  let proc ← findProc result "matrix"
  let some m := proc.inputs.find? (fun (p : Strata.Laurel.Parameter) => p.name.text == "m")
    | throw <| IO.userError "m not found"
  IO.println (shape m.type.val)

/-! ## Pyspec refusals under `--typed-python` -/

-- `bytes` is not in the supported set.
#guard_msgs(drop info) in
#eval do
  let msg ← expectRefusal #[
    mkFunc "raw" #[mkArg "b" (identType .builtinsBytes)] (identType .builtinsInt)
  ]
  unless msg.length > 0 do throw <| IO.userError "no diagnostic"

-- `Optional[int]` (Union[int, None]) is refused.
#guard_msgs(drop info) in
#eval do
  let msg ← expectRefusal #[
    mkFunc "uses_optional"
      #[mkArg "x" (SpecType.unionArray loc
          #[identType .builtinsInt, identType .noneType])]
      (identType .builtinsInt)
  ]
  unless msg.length > 0 do throw <| IO.userError "no diagnostic"

/-! ## Native preconditions emit native operators -/

-- `assert x >= 0` over a typed `int` parameter does NOT contain
-- `Any..isfrom_int` or `Any..as_int!` — the comparison is direct.
/-- info: native: 0 isfrom_int / 0 as_int! -/
#guard_msgs in
#eval do
  let result ← buildSpecs #[
    mkFunc "check_nonneg"
      #[mkArg "x" (identType .builtinsInt)]
      (identType .builtinsInt)
      #[assertionOf (.intGe (.var "x" loc) (.intLit 0 loc) loc)]
  ] (typedPython := true)
  let proc ← findProc result "check_nonneg"
  let body := toString (formatProcedure proc)
  let count (needle : String) : Nat :=
    (body.splitOn needle).length - 1
  IO.println s!"native: {count "Any..isfrom_int"} isfrom_int / {count "Any..as_int!"} as_int!"

-- Default mode contains the Any-tag obligations.
/-- info: any: 2 isfrom_int / 1 as_int! -/
#guard_msgs in
#eval do
  let result ← buildSpecs #[
    mkFunc "check_nonneg"
      #[mkArg "x" (identType .builtinsInt)]
      (identType .builtinsInt)
      #[assertionOf (.intGe (.var "x" loc) (.intLit 0 loc) loc)]
  ] (typedPython := false)
  let proc ← findProc result "check_nonneg"
  let body := toString (formatProcedure proc)
  let count (needle : String) : Nat :=
    (body.splitOn needle).length - 1
  IO.println s!"any: {count "Any..isfrom_int"} isfrom_int / {count "Any..as_int!"} as_int!"

end Strata.Python.TypedPythonTest
