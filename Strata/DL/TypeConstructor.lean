/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTy

open Std (ToFormat Format format)

public section

/-! # Type Constructor

A type constructor declaration that can be shared across dialects.
-/

inductive Boundedness where
  | Finite
  | Infinite -- Default
  deriving Repr

structure TypeConstructor where
  -- (TODO) Add SMT support for Boogie's Finite types.
  bound    : Boundedness := .Infinite
  name     : String
  params   : List String
  deriving Repr

def TypeConstructor.numargs (t : TypeConstructor) : Nat := t.params.length

instance : ToFormat TypeConstructor where
  format t :=
    let args := (if t.params.isEmpty then [] else t.params).toString
    f!"type {repr t.bound} {t.name} {args}"

def TypeConstructor.toType (t : TypeConstructor) : Lambda.LTy :=
  if t.params.isEmpty then
    .forAll [] (.tcons t.name [])
  else
    .forAll t.params (.tcons t.name (t.params.map Lambda.LMonoTy.ftvar))

end -- public section
