/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.TypeFactory

namespace Lambda

open Std (ToFormat Format format)

/-! # Lambda Dialect

The Lambda dialect provides an implementation of simply-typed lambda
calculus, along with a Hindley-Milner type system. It also comes with an
extensible partial evaluator that is parameterized by an (optional) map from
operator names to their specific evaluations. This allows adding evaluation
support for new operators without changing the core logic or extending the AST.

See module `Strata.DL.Lambda.LExpr` for the formalization of expressions,
`Strata.DL.Lambda.LTy` for the formalization of mono- and poly-types,
`Strata.DL.Lambda.LExprT` for the type inference implementation, and
`Strata.DL.Lambda.LExprEval` for the partial evaluator.
-/

variable {Identifier : Type} [ToString Identifier] [DecidableEq Identifier] [ToFormat Identifier] [HasGen Identifier] [Coe String Identifier]

def LDatatype.toKnownType (d: LDatatype Identifier) : KnownType :=
  { name := d.name, arity := d.typeArgs.length}

def TypeFactory.toKnownTypes (t: @TypeFactory Identifier) : List KnownType :=
  t.foldr (fun t l => t.toKnownType :: l) []

/--
Top-level type checking and partial evaluation function for the Lambda
dialect.
-/
def typeCheckAndPartialEval
  (genArgNames : Nat -> List Identifier := fun _ => []) --TODO bad hack
  (t: TypeFactory (Identifier:=Identifier) := TypeFactory.default)
  (f : Factory (Identifier:=Identifier) := Factory.default)
  (e : (LExpr LMonoTy Identifier)) :
  Except Std.Format (LExpr LMonoTy Identifier) := do
  let fTy ← t.genFactory genArgNames
  let fAll ← Factory.addFactory fTy f
  let T := TEnv.default.addFactoryFunctions fAll
  let T := T.addKnownTypes t.toKnownTypes
  let (et, _T) ← LExpr.annotate T e
  dbg_trace f!"Annotated expression:{Format.line}{et}{Format.line}"
  let σ ← (LState.init).addFactory fAll
  return (LExpr.eval σ.config.fuel σ et)

end Lambda

---------------------------------------------------------------------
