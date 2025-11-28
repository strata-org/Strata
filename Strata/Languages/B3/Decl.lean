/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Expression
import Strata.Languages.B3.Stmt
import Strata.Languages.B3.Identifiers

---------------------------------------------------------------------

namespace B3

---------------------------------------------------------------------

structure DeclParams : Type 1 where
  Metadata : Type
  IDMeta : Type

abbrev DeclParams.Identifier (P : DeclParams) : Type := Lambda.Identifier P.IDMeta

def DeclParams.toExprParams (P : DeclParams) : ExprParams := {
  Metadata := P.Metadata
  IDMeta := P.IDMeta
}

def DeclParams.toStmtParams (P : DeclParams) : StmtParams := {
  Metadata := P.Metadata
  exprParams := P.toExprParams
}

inductive ParamMode where
  | «in»
  | out
  | inout
  deriving DecidableEq

instance : Repr ParamMode where
  reprPrec m _ := match m with
    | .«in» => ".in"
    | .out => ".out"
    | .inout => ".inout"

inductive FParameter (P : DeclParams) : Type where
  | mk (injective : Bool) (name : P.Identifier) (ty : P.Identifier) : FParameter P

inductive PParameter (P : DeclParams) : Type where
  | mk (mode : ParamMode) (name : P.Identifier) (ty : P.Identifier) (autoinv : Option (Expression P.toExprParams)) : PParameter P

inductive Spec (P : DeclParams) : Type where
  | requires (md : P.Metadata) (expr : Expression P.toExprParams) : Spec P
  | ensures (md : P.Metadata) (expr : Expression P.toExprParams) : Spec P

inductive Decl (P : DeclParams) : Type where
  | typeDecl
      (md : P.Metadata)
      (name : P.Identifier)
      : Decl P
  | tagger
      (md : P.Metadata)
      (name : P.Identifier)
      (forType : P.Identifier)
      : Decl P
  | function
      (md : P.Metadata)
      (name : P.Identifier)
      (params : List (FParameter P))
      (resultType : P.Identifier)
      (tag : Option P.Identifier)
      (whens : List (Expression P.toExprParams))
      (body : Option (Expression P.toExprParams))
      : Decl P
  | axiom
      (md : P.Metadata)
      (explains : List P.Identifier)
      (expr : Expression P.toExprParams)
      : Decl P
  | procedure
      (md : P.Metadata)
      (name : P.Identifier)
      (params : List (PParameter P))
      (specs : List (Spec P))
      (body : Option (Stmt P.toStmtParams))
      : Decl P

---------------------------------------------------------------------
-- Default DeclParams
---------------------------------------------------------------------

/-- Default DeclParams with Unit metadata and B3IdentifierMetadata -/
def defaultDeclParams : DeclParams where
  Metadata := Unit
  IDMeta := B3IdentifierMetadata

/-- B3 Declaration with default parameters -/
abbrev B3Decl := Decl defaultDeclParams
abbrev B3FParameter := FParameter defaultDeclParams
abbrev B3PParameter := PParameter defaultDeclParams
abbrev B3Spec := Spec defaultDeclParams

---------------------------------------------------------------------
-- Repr Instances
---------------------------------------------------------------------

instance : Repr Unit where
  reprPrec _ _ := "()"

instance : Repr B3IdentifierMetadata where
  reprPrec _ _ := "()"

instance : Repr (Lambda.Identifier B3IdentifierMetadata) where
  reprPrec id _ := id.name

partial def B3FParameter.repr (p : B3FParameter) : String :=
  match p with
  | .mk injective name ty => s!".mk {reprArg injective} {reprArg name} {reprArg ty}"

partial def B3PParameter.repr (p : B3PParameter) : String :=
  match p with
  | .mk mode name ty autoinv =>
      let autoinvRepr := match autoinv with
        | some e => s!"(some ({Expression.repr e}))"
        | none => "none"
      s!".mk {reprArg mode} {reprArg name} {reprArg ty} {autoinvRepr}"

partial def B3Spec.repr (s : B3Spec) : String :=
  match s with
  | .requires md expr => s!".requires {reprArg md} ({Expression.repr expr})"
  | .ensures md expr => s!".ensures {reprArg md} ({Expression.repr expr})"

partial def B3Decl.repr (d : B3Decl) : String :=
  match d with
  | .typeDecl md name => s!".typeDecl {reprArg md} {reprArg name}"
  | .tagger md name forType => s!".tagger {reprArg md} {reprArg name} {reprArg forType}"
  | .function md name params resultType tag whens body =>
      let paramsRepr := "[" ++ String.intercalate ", " (params.map B3FParameter.repr) ++ "]"
      let tagRepr := match tag with | some t => s!"(some {reprArg t})" | none => "none"
      let whensRepr := "[" ++ String.intercalate ", " (whens.map Expression.repr) ++ "]"
      let bodyRepr := match body with | some e => s!"(some ({Expression.repr e}))" | none => "none"
      s!".function {reprArg md} {reprArg name} {paramsRepr} {reprArg resultType} {tagRepr} {whensRepr} {bodyRepr}"
  | .axiom md explains expr =>
      let explainsRepr := "[" ++ String.intercalate ", " (explains.map repr) ++ "]"
      s!".axiom {reprArg md} {explainsRepr} ({Expression.repr expr})"
  | .procedure md name params specs body =>
      let paramsRepr := "[" ++ String.intercalate ", " (params.map B3PParameter.repr) ++ "]"
      let specsRepr := "[" ++ String.intercalate ", " (specs.map B3Spec.repr) ++ "]"
      let bodyRepr := match body with | some s => s!"(some ({Stmt.repr s}))" | none => "none"
      s!".procedure {reprArg md} {reprArg name} {paramsRepr} {specsRepr} {bodyRepr}"

instance : Repr B3Decl where
  reprPrec d _ := B3Decl.repr d

instance : Repr B3FParameter where
  reprPrec p _ := B3FParameter.repr p

instance : Repr B3PParameter where
  reprPrec p _ := B3PParameter.repr p

instance : Repr B3Spec where
  reprPrec s _ := B3Spec.repr s

end B3
