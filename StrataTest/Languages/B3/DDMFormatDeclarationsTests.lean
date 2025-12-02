/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests
import StrataTest.Languages.B3.DDMFormatStatementsTests
import Strata.Languages.B3.DDMConversion

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

partial def doRoundtripDecl (decl : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Decl.ofAst decl with
  | .ok cstDecl =>
      let b3Decl := Decl.toAST cstDecl
      let b3DeclUnit := b3Decl.toUnit
      let reprStr := (repr b3DeclUnit).pretty.replace "Strata.B3AST.Decl." "."
      let reprStr := reprStr.replace "Strata.B3AST.FParameter." "."
      let reprStr := reprStr.replace "Strata.B3AST.PParameter." "."
      let reprStr := reprStr.replace "Strata.B3AST.Spec." "."
      let reprStr := reprStr.replace "Strata.B3AST.ParamMode." "."
      let reprStr := reprStr.replace "Strata.B3AST.Expression." "."
      let reprStr := reprStr.replace "Strata.B3AST.Literal." "."
      let reprStr := reprStr.replace "Strata.B3AST.UnaryOp." "."
      let reprStr := reprStr.replace "Strata.B3AST.BinaryOp." "."
      let reprStr := reprStr.replace "Strata.B3AST.Statement." "."
      let reprStr := reprStr.replace "Strata.B3AST.CallArg." "."
      dbg_trace f!"B3: {reprStr}"
      let cstDecl' := Decl.toCST b3Decl
      let cstAst := cstDecl'.toAst
      cformat (ArgF.op cstAst) ctx state
  | .error msg => s!"Parse error: {msg}"

partial def doRoundtripProgram (prog : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Program.ofAst prog with
  | .ok cstProg =>
      let b3Prog := Program.toAST cstProg
      let b3ProgUnit := b3Prog.toUnit
      let reprStr := (repr b3ProgUnit).pretty.replace "Strata.B3AST.Program." "."
      let reprStr := reprStr.replace "Strata.B3AST.Decl." "."
      let reprStr := reprStr.replace "Strata.B3AST.FParameter." "."
      let reprStr := reprStr.replace "Strata.B3AST.PParameter." "."
      let reprStr := reprStr.replace "Strata.B3AST.Spec." "."
      let reprStr := reprStr.replace "Strata.B3AST.ParamMode." "."
      let reprStr := reprStr.replace "Strata.B3AST.Expression." "."
      let reprStr := reprStr.replace "Strata.B3AST.Literal." "."
      let reprStr := reprStr.replace "Strata.B3AST.UnaryOp." "."
      let reprStr := reprStr.replace "Strata.B3AST.BinaryOp." "."
      let reprStr := reprStr.replace "Strata.B3AST.Statement." "."
      let reprStr := reprStr.replace "Strata.B3AST.CallArg." "."
      let reprStr := reprStr.replace "Strata.B3AST.FunctionBody." "."
      let reprStr := reprStr.replace "Strata.B3AST.When." "."
      dbg_trace f!"B3: {reprStr}"
      let cstProg' := Program.toCST b3Prog
      let cstAst := cstProg'.toAst
      cformat (ArgF.op cstAst) ctx state
  | .error msg => s!"Parse error: {msg}"

def roundtripDecl (p : Program) : Format :=
  let ctx := p.formatContext {}
  let state := p.formatState
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
info: B3: .program () { ann := (), val := #[.typeDecl () { ann := (), val := "MyType" }] }
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
  { ann := (), val := #[.tagger () { ann := (), val := "MyTagger" } { ann := (), val := "MyType" }] }
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
  { ann := (),
    val := #[.axiom
               ()
               { ann := (), val := #[] }
               (.literal () (.boolLit () { ann := (), val := true }))] }
---
info:
axiom true
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; axiom true #end

/--
info: B3: .program
  ()
  { ann := (),
    val := #[.function
               ()
               { ann := (), val := "F" }
               { ann := (),
                 val := #[.fParameter
                            ()
                            { ann := (), val := false }
                            { ann := (), val := "x" }
                            { ann := (), val := "int" }] }
               { ann := (), val := "int" }
               { ann := (), val := none }
               { ann := (),
                 val := some (.functionBody
                          ()
                          { ann := (), val := #[] }
                          (.literal
                            ()
                            (.intLit () { ann := (), val := 1 }))) }] }
---
info:
function F(()x : int) : int(() {
  1
})
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function F(x: int) : int { 1 } #end

-- Function with multiple parameters
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function add(x: int, y: int) : int { x + y } #end

-- Function with injective parameter
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function id(injective x: int) : int { x } #end

-- Function with tag
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function tagged(x: int) : int tag mytag { x } #end

-- Function with when clause
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; function conditional(x: int) : int when x > 0 { x } #end

-- Simple procedure with no parameters
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure noop() { return } #end

-- Procedure with in parameter
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure process(x: int) { check x > 0 } #end

-- Procedure with out parameter
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure getResult(out result: int) { result := 42 } #end

-- Procedure with inout parameter
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure increment(inout x: int) { x := x + 1 } #end

-- Procedure with mixed parameters
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure compute(x: int, out y: int, inout z: int) { y := x + z z := z + 1 } #end

-- Procedure with requires spec
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure safe(x: int) requires x > 0 { check x > 0 } #end

-- Procedure with ensures spec
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure positive(out x: int) ensures x > 0 { x := 1 } #end

-- Procedure with both requires and ensures
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure bounded(x: int, out y: int) requires x >= 0 ensures y >= 0 { y := x } #end

-- Procedure with parameter autoinv
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure withAutoinv(x: int autoinv x >= 0) { check x >= 0 } #end

-- Procedure with body containing multiple statements
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; procedure multi(x: int, out y: int) { var temp : int temp := x + 1 y := temp * 2 } #end

-- Multiple declarations in a program
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; type T axiom true function f(x: int) : int { x } #end

end DeclarationRoundtripTests

end B3
