/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Declaration Formatting Tests

Tests for round-trip conversion and formatting of B3 declarations (types, functions, axioms, procedures).
Verifies that DDM AST → B3 AST → B3 CST → formatted output preserves structure and catches conversion errors.
-/

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

partial def doRoundtripDecl (decl : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Decl.ofAst decl with
  | .ok cstDecl =>
      let (b3Decl, cstToAstErrors) := B3.declFromCST B3.FromCSTContext.empty cstDecl
      let (cstDecl', astToCstErrors) := B3.declToCST B3.ToCSTContext.empty b3Decl
      -- Convert to Unit metadata for repr
      let b3DeclUnit := B3AST.Decl.mapMetadata (fun _ => ()) b3Decl
      let reprStr := (repr b3DeclUnit).pretty
      let reprStr := cleanupDeclRepr reprStr
      let reprStr := cleanupUnitRepr reprStr
      let errorStr := if cstToAstErrors.isEmpty && astToCstErrors.isEmpty then ""
        else
          let cstErrs := cstToAstErrors.map Std.format |> List.map (·.pretty) |> String.intercalate "\n  "
          let astErrs := astToCstErrors.map Std.format |> List.map (·.pretty) |> String.intercalate "\n  "
          let parts := [
            if cstToAstErrors.isEmpty then "" else s!"\nCST→AST Errors:\n  {cstErrs}",
            if astToCstErrors.isEmpty then "" else s!"\nAST→CST Errors:\n  {astErrs}"
          ]
          String.join parts
      dbg_trace f!"B3: {reprStr}{errorStr}"
      let cstAst := cstDecl'.toAst
      (mformat (ArgF.op cstAst) ctx state).format
  | .error msg => s!"Parse error: {msg}"

partial def doRoundtripProgram (prog : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) (printIntermediate: Bool := true) : Format :=
  match B3CST.Program.ofAst prog with
  | .ok cstProg =>
      let (b3Prog, cstToAstErrors) := B3.programFromCST B3.FromCSTContext.empty cstProg
      let (cstProg', astToCstErrors) := B3.programToCST B3.ToCSTContext.empty b3Prog
      let errorStr := if cstToAstErrors.isEmpty && astToCstErrors.isEmpty then ""
        else
          let cstErrs := cstToAstErrors.map Std.format |> List.map (·.pretty) |> String.intercalate "\n  "
          let astErrs := astToCstErrors.map Std.format |> List.map (·.pretty) |> String.intercalate "\n  "
          let parts := [
            if cstToAstErrors.isEmpty then "" else s!"\nCST→AST Errors:\n  {cstErrs}",
            if astToCstErrors.isEmpty then "" else s!"\nAST→CST Errors:\n  {astErrs}"
          ]
          String.join parts
      dbg_trace (if printIntermediate then
          -- Convert to Unit metadata for repr
          let b3ProgUnit := B3AST.Program.mapMetadata (fun _ => ()) b3Prog
          let reprStr := (repr b3ProgUnit).pretty
          let reprStr := cleanupDeclRepr reprStr
          let reprStr := cleanupUnitRepr reprStr
          f!"B3: {reprStr}{errorStr}"
        else
          f!"<B3 omitted>{errorStr}")
      let cstAst := cstProg'.toAst
      (mformat (ArgF.op cstAst) ctx state).format
  | .error msg => s!"Parse error: {msg}"

def roundtripDecl (p : Program) : Format :=
  let ctx := FormatContext.ofDialects p.dialects p.globalContext {}
  let state : FormatState := { openDialects := p.dialects.toList.foldl (init := {}) fun a d => a.insert d.name }
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_program" then
      match op.args.toList with
      | [ArgF.op prog] => doRoundtripProgram prog ctx state
      | _ => "Error: expected program op"
    else s!"Error: expected command_program, got {op.name.name}"
  | _ => "Error: expected single command"



section DeclarationRoundtripTests

-- Type declaration
/--
info: B3: .program () u #[.typeDecl () u "MyType"]
---
info:
type MyType
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; type MyType #end

-- Tagger declaration
/--
info: B3: .program
  ()
  u #[.tagger () u "MyTagger" u "MyType"]
---
info:
tagger MyTagger for MyType
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; tagger MyTagger for MyType #end

-- Simple axiom
/--
info: B3: .program
  ()
  u #[.axiom
    ()
    u #[]
    (.literal () (.boolLit () true))]
---
info:
axiom true
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; axiom true #end

/--
info: B3: .program
  ()
  u #[.function
    ()
    u "F"
    u #[.fParameter
      ()
      u false
      u "x"
      u "int"]
    u "int"
    u none
    u some (.functionBody
      ()
      u #[]
      (.literal () (.intLit () 1)))]
---
info:
function F(x : int) : int {
  1
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function F(x: int) : int { 1 } #end

-- Function with multiple parameters
/--
info: B3: .program
  ()
  u #[.function
    ()
    u "add"
    u #[.fParameter
      ()
      u false
      u "x"
      u "int",
    .fParameter
      ()
      u false
      u "y"
      u "int"]
    u "int"
    u none
    u some (.functionBody
      ()
      u #[]
      (.binaryOp
        ()
        (.add ())
        (.id () 1)
        (.id () 0)))]
---
info:
function add(x : int, y : int) : int {
  x + y
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function add(x: int, y: int) : int { x + y } #end

-- Function with injective parameter
/--
info: B3: .program
  ()
  u #[.function
    ()
    u "id"
    u #[.fParameter
      ()
      u true
      u "x"
      u "int"]
    u "int"
    u none
    u some (.functionBody
      ()
      u #[]
      (.id () 0))]
---
info:
function id(injective x : int) : int {
  x
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function id(injective x: int) : int { x } #end

-- Function with tag
/--
info: B3: .program
  ()
  u #[.function
    ()
    u "tagged"
    u #[.fParameter
      ()
      u false
      u "x"
      u "int"]
    u "int"
    u some u "mytag"
    u some (.functionBody
      ()
      u #[]
      (.id () 0))]
---
info:
function tagged(x : int) : int tag mytag {
  x
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function tagged(x: int) : int tag mytag { x } #end

-- Function with when clause
/--
info: B3: .program
  ()
  u #[.function
    ()
    u "conditional"
    u #[.fParameter
      ()
      u false
      u "x"
      u "int"]
    u "int"
    u none
    u some (.functionBody
      ()
      u #[.when
        ()
        (.binaryOp
          ()
          (.gt ())
          (.id () 0)
          (.literal () (.intLit () 0)))]
      (.id () 0))]
---
info:
function conditional(x : int) : int
  when x > 0 {
  x
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function conditional(x: int) : int when x > 0 { x } #end

-- Simple procedure with no parameters
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "noop"
    u #[]
    u #[]
    u some (.blockStmt
      ()
      u #[.returnStmt ()])]
---
info:
procedure noop()
{
  return
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure noop() { return } #end

-- Procedure with in parameter
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "process"
    u #[.pParameter
      ()
      (.paramModeIn ())
      u "x"
      u "int"
      u none]
    u #[]
    u some (.blockStmt
      ()
      u #[.check
        ()
        (.binaryOp
          ()
          (.gt ())
          (.id () 0)
          (.literal
            ()
            (.intLit () 0)))])]
---
info:
procedure process(x : int)
{
  check x > 0
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure process(x: int) { check x > 0 } #end

-- Procedure with out parameter
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "getResult"
    u #[.pParameter
      ()
      (.paramModeOut ())
      u "result"
      u "int"
      u none]
    u #[]
    u some (.blockStmt
      ()
      u #[.assign
        ()
        u 0
        (.literal () (.intLit () 42))])]
---
info:
procedure getResult(out result : int)
{
  result := 42
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure getResult(out result: int) { result := 42 } #end

-- Procedure with inout parameter
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "increment"
    u #[.pParameter
      ()
      (.paramModeInout ())
      u "x"
      u "int"
      u none]
    u #[.specEnsures
      ()
      (.binaryOp
        ()
        (.eq ())
        (.id () 0)
        (.binaryOp
          ()
          (.add ())
          (.id () 1)
          (.literal () (.intLit () 1))))]
    u some (.blockStmt
      ()
      u #[.assert
        ()
        (.binaryOp
          ()
          (.eq ())
          (.id () 0)
          (.id () 1)),
      .assign
        ()
        u 0
        (.binaryOp
          ()
          (.add ())
          (.id () 0)
          (.literal () (.intLit () 1))),
      .assert
        ()
        (.binaryOp
          ()
          (.eq ())
          (.id () 0)
          (.binaryOp
            ()
            (.add ())
            (.id () 1)
            (.literal
              ()
              (.intLit () 1))))])]
---
info:
procedure increment(inout x : int)
  ensures x == old x + 1
{
  assert x == old x
  x := x + 1
  assert x == old x + 1
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure increment(inout x: int) ensures x == old x + 1 { assert x == old x
  x := x + 1
  assert x == old x + 1
} #end

-- Procedure with mixed parameters
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "compute"
    u #[.pParameter
      ()
      (.paramModeIn ())
      u "x"
      u "int"
      u none,
    .pParameter
      ()
      (.paramModeOut ())
      u "y"
      u "int"
      u none,
    .pParameter
      ()
      (.paramModeInout ())
      u "z"
      u "int"
      u none]
    u #[]
    u some (.blockStmt
      ()
      u #[.assign
        ()
        u 2
        (.binaryOp
          ()
          (.add ())
          (.id () 3)
          (.id () 0)),
      .assign
        ()
        u 0
        (.binaryOp
          ()
          (.add ())
          (.id () 0)
          (.literal
            ()
            (.intLit () 1)))])]
---
info:
procedure compute(x : int, out y : int, inout z : int)
{
  y := x + z
  z := z + 1
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure compute(x: int, out y: int, inout z: int) { y := x + z z := z + 1 } #end

-- Procedure with requires spec
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "safe"
    u #[.pParameter
      ()
      (.paramModeIn ())
      u "x"
      u "int"
      u none]
    u #[.specRequires
      ()
      (.binaryOp
        ()
        (.gt ())
        (.id () 0)
        (.literal () (.intLit () 0)))]
    u some (.blockStmt
      ()
      u #[.check
        ()
        (.binaryOp
          ()
          (.gt ())
          (.id () 0)
          (.literal
            ()
            (.intLit () 0)))])]
---
info:
procedure safe(x : int)
  requires x > 0
{
  check x > 0
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure safe(x: int) requires x > 0 { check x > 0 } #end

-- Procedure with ensures spec
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "positive"
    u #[.pParameter
      ()
      (.paramModeOut ())
      u "x"
      u "int"
      u none]
    u #[.specEnsures
      ()
      (.binaryOp
        ()
        (.gt ())
        (.id () 0)
        (.literal () (.intLit () 0)))]
    u some (.blockStmt
      ()
      u #[.assign
        ()
        u 0
        (.literal () (.intLit () 1))])]
---
info:
procedure positive(out x : int)
  ensures x > 0
{
  x := 1
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure positive(out x: int) ensures x > 0 { x := 1 } #end

-- Procedure with both requires and ensures
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "bounded"
    u #[.pParameter
      ()
      (.paramModeIn ())
      u "x"
      u "int"
      u none,
    .pParameter
      ()
      (.paramModeOut ())
      u "y"
      u "int"
      u none]
    u #[.specRequires
      ()
      (.binaryOp
        ()
        (.ge ())
        (.id () 1)
        (.literal () (.intLit () 0))),
    .specEnsures
      ()
      (.binaryOp
        ()
        (.ge ())
        (.id () 0)
        (.literal () (.intLit () 0)))]
    u some (.blockStmt
      ()
      u #[.assign
        ()
        u 0
        (.id () 1)])]
---
info:
procedure bounded(x : int, out y : int)
  requires x >= 0
  ensures y >= 0
{
  y := x
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure bounded(x: int, out y: int) requires x >= 0 ensures y >= 0 { y := x } #end

-- Procedure with parameter autoinv
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "withAutoinv"
    u #[.pParameter
      ()
      (.paramModeIn ())
      u "x"
      u "int"
      u some (.binaryOp
        ()
        (.ge ())
        (.binaryOp
          ()
          (.add ())
          (.id () 1)
          (.id () 0))
        (.literal () (.intLit () 0))),
    .pParameter
      ()
      (.paramModeIn ())
      u "y"
      u "int"
      u some (.binaryOp
        ()
        (.ge ())
        (.id () 0)
        (.unaryOp
          ()
          (.neg ())
          (.id () 1)))]
    u #[]
    u some (.blockStmt
      ()
      u #[.check
        ()
        (.binaryOp
          ()
          (.ge ())
          (.id () 1)
          (.literal
            ()
            (.intLit () 0)))])]
---
info:
procedure withAutoinv(x : int autoinv x + y >= 0, y : int autoinv y >= -(x))
{
  check x >= 0
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure withAutoinv(x: int autoinv x + y >= 0, y: int autoinv y >= -x) { check x >= 0 } #end

-- Procedure with body containing multiple statements
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "multi"
    u #[.pParameter
      ()
      (.paramModeIn ())
      u "x"
      u "int"
      u none,
    .pParameter
      ()
      (.paramModeOut ())
      u "y"
      u "int"
      u none]
    u #[]
    u some (.blockStmt
      ()
      u #[.varDecl
        ()
        u "temp"
        u some u "int"
        u none
        u none,
      .assign
        ()
        u 0
        (.binaryOp
          ()
          (.add ())
          (.id () 2)
          (.literal () (.intLit () 1))),
      .assign
        ()
        u 1
        (.binaryOp
          ()
          (.mul ())
          (.id () 0)
          (.literal
            ()
            (.intLit () 2)))])]
---
info:
procedure multi(x : int, out y : int)
{
  var temp : int
  temp := x + 1
  y := temp * 2
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure multi(x: int, out y: int) { var temp : int temp := x + 1 y := temp * 2 } #end

-- Multiple declarations in a program
/--
info: B3: .program
  ()
  u #[.typeDecl () u "T",
    .axiom
      ()
      u #[]
      (.literal () (.boolLit () true)),
    .function
      ()
      u "f"
      u #[.fParameter
        ()
        u false
        u "x"
        u "int"]
      u "int"
      u none
      u some (.functionBody
        ()
        u #[]
        (.id () 0))]
---
info:
type T
axiom true
function f(x : int) : int {
  x
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; type T axiom true function f(x: int) : int { x } #end

-- Procedure with inout parameter using old values in spec and body
/--
info: B3: .program
  ()
  u #[.procedure
    ()
    u "incrementWithOld"
    u #[.pParameter
      ()
      (.paramModeInout ())
      u "x"
      u "int"
      u none]
    u #[.specEnsures
      ()
      (.binaryOp
        ()
        (.eq ())
        (.id () 0)
        (.binaryOp
          ()
          (.add ())
          (.id () 1)
          (.literal () (.intLit () 1))))]
    u some (.blockStmt
      ()
      u #[.assign
        ()
        u 0
        (.binaryOp
          ()
          (.add ())
          (.id () 0)
          (.literal () (.intLit () 1))),
      .assert
        ()
        (.binaryOp
          ()
          (.eq ())
          (.id () 0)
          (.binaryOp
            ()
            (.add ())
            (.id () 1)
            (.literal
              ()
              (.intLit () 1))))])]
---
info:
procedure incrementWithOld(inout x : int)
  ensures x == old x + 1
{
  x := x + 1
  assert x == old x + 1
}
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST;
procedure incrementWithOld(inout x: int)
  ensures x == old x + 1
{
  x := x + 1
  assert x == old x + 1
}
#end

end DeclarationRoundtripTests

end B3
