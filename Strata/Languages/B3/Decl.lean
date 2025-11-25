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
  deriving Repr, DecidableEq

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

end B3
