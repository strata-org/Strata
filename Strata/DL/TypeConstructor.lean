/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy

namespace Strata

open Std (ToFormat Format format)
open Lambda

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
  -- Boogie treats
  -- `type Foo a a;` // or type Foo _ _;
  -- the same as
  -- `type Foo a b;`
  -- That is, the exact identifier is irrelevant. As such, we only
  -- record the number of arguments in a type constructor here.
  numargs  : Nat
  deriving Repr

instance : ToFormat TypeConstructor where
  format t :=
    let args := (List.replicate t.numargs "_").toString
    f!"type {repr t.bound} {t.name} {args}"

def TypeConstructor.toType (t : TypeConstructor) : LTy :=
  let typeargs := List.replicate t.numargs "_ty"
  let ids := typeargs.mapIdx (fun i elem => (elem ++ toString i))
  let args := typeargs.mapIdx (fun i elem => LMonoTy.ftvar (elem ++ toString i))
  .forAll ids (.tcons t.name args)

end Strata
