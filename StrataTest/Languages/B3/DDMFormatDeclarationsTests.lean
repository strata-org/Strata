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

mutual
  partial def stripDeclAnnotations : B3CST.Decl SourceRange → B3CST.Decl Unit
    | .type_decl _ name =>
        .type_decl () ⟨(), name.val⟩
    | .tagger_decl _ name forType =>
        .tagger_decl () ⟨(), name.val⟩ ⟨(), forType.val⟩
    | .function_decl _ name params resultType tag body =>
        .function_decl () ⟨(), name.val⟩ ⟨(), params.val.map stripFParamAnnotations⟩ ⟨(), resultType.val⟩ ⟨(), tag.val.map stripTagClauseAnnotations⟩ ⟨(), body.val.map stripFunctionBodyAnnotations⟩
    | .axiom_decl _ axiomBody =>
        .axiom_decl () (stripAxiomBodyAnnotations axiomBody)
    | .procedure_decl _ name params specs body =>
        .procedure_decl () ⟨(), name.val⟩ ⟨(), params.val.map stripPParamAnnotations⟩ ⟨(), specs.val.map stripSpecAnnotations⟩ ⟨(), body.val.map stripProcBodyAnnotations⟩

  partial def stripFParamAnnotations : B3CST.FParam SourceRange → B3CST.FParam Unit
    | .fparam _ injective name ty =>
        .fparam () ⟨(), injective.val.map stripInjectiveAnnotations⟩ ⟨(), name.val⟩ ⟨(), ty.val⟩

  partial def stripInjectiveAnnotations : B3CST.Injective SourceRange → B3CST.Injective Unit
    | .injective_some _ => .injective_some ()

  partial def stripPParamAnnotations : B3CST.PParam SourceRange → B3CST.PParam Unit
    | .pparam _ mode name ty =>
        .pparam () ⟨(), mode.val.map stripPParamModeAnnotations⟩ ⟨(), name.val⟩ ⟨(), ty.val⟩
    | .pparam_with_autoinv _ mode name ty autoinv =>
        .pparam_with_autoinv () ⟨(), mode.val.map stripPParamModeAnnotations⟩ ⟨(), name.val⟩ ⟨(), ty.val⟩ (stripAnnotations autoinv)

  partial def stripPParamModeAnnotations : B3CST.PParamMode SourceRange → B3CST.PParamMode Unit
    | .pmode_out _ => .pmode_out ()
    | .pmode_inout _ => .pmode_inout ()

  partial def stripSpecAnnotations : B3CST.Spec SourceRange → B3CST.Spec Unit
    | .spec_requires _ expr => .spec_requires () (stripAnnotations expr)
    | .spec_ensures _ expr => .spec_ensures () (stripAnnotations expr)

  partial def stripTagClauseAnnotations : B3CST.TagClause SourceRange → B3CST.TagClause Unit
    | .tag_some _ t => .tag_some () ⟨(), t.val⟩

  partial def stripWhenClauseAnnotations : B3CST.WhenClause SourceRange → B3CST.WhenClause Unit
    | .when_clause _ expr => .when_clause () (stripAnnotations expr)

  partial def stripFunctionBodyAnnotations : B3CST.FunctionBody SourceRange → B3CST.FunctionBody Unit
    | .function_body_some _ whens expr => .function_body_some () ⟨(), whens.val.map stripWhenClauseAnnotations⟩ (stripAnnotations expr)

  partial def stripAxiomBodyAnnotations : B3CST.AxiomBody SourceRange → B3CST.AxiomBody Unit
    | .axiom _ expr => .axiom () (stripAnnotations expr)
    | .explain_axiom _ names expr => .explain_axiom () ⟨(), names.val.map (fun n => ⟨(), n.val⟩)⟩ (stripAnnotations expr)

  partial def stripProcBodyAnnotations : B3CST.ProcBody SourceRange → B3CST.ProcBody Unit
    | .proc_body_some _ stmt => .proc_body_some () (stripStmtAnnotations stmt)
end

def doRoundtripDecl (decl : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Decl.ofAst decl with
  | .ok cstDecl =>
      let cstDeclUnit := stripDeclAnnotations cstDecl
      let b3Decl := Decl.fromDDM cstDeclUnit
      let reprStr := (repr b3Decl).pretty.replace "Strata.B3AST.Decl." "."
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
      let cstDecl' := b3Decl.toDDM
      let cstAst := cstDecl'.toAst
      let cstAstSR := argFUnitToSourceRange (ArgF.op cstAst)
      cformat cstAstSR ctx state
  | .error msg => s!"Parse error: {msg}"

def roundtripDecl (p : Program) : Format :=
  let ctx := p.formatContext {}
  let state := p.formatState
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_decl" then
      match op.args.toList with
      | [ArgF.op decl] => doRoundtripDecl decl ctx state
      | _ => "Error: expected decl op"
    else s!"Error: expected command_decl, got {op.name.name}"
  | _ => "Error: expected single command"

section DeclarationRoundtripTests

-- Type declaration
/--
info: B3: .typeDecl () { ann := (), val := "MyType" }
---
info: type MyType
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; type MyType #end

-- Tagger declaration
/--
info: B3: .tagger () { ann := (), val := "MyTagger" } { ann := (), val := "MyType" }
---
info:
tagger MyTagger for MyType
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; tagger MyTagger for MyType #end

-- Simple axiom
/--
info: B3: .axiom
  ()
  { ann := (), val := #[] }
  (.literal () (.boolLit () { ann := (), val := true }))
---
info:
axiom true
-/
#guard_msgs in
#eval roundtripDecl $ #strata program B3CST; axiom true #end

-- TODO: Fix function body formatting
-- #guard_msgs in
-- #eval roundtripDecl $ #strata program B3CST; function F(x: int) : int { 1 } #end

end DeclarationRoundtripTests

end B3
