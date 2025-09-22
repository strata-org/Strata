/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy

/-! ## Lambda Types with Bounded Ints
-/

-- The grammar allows expressions like a <= b /\ b < c, where a, b, and c
-- are integer constants or a (single) variable. This lets us express e.g.
-- {x | 0 <= x < 2^32}

namespace Bounded
open Std (ToFormat Format format)


abbrev TyIdentifier := String

inductive BVal : Type where
  /-- The bounded variable -/
  | bvar
  /-- Integer constants -/
  | bconst (val: Int)
deriving Inhabited, Repr, DecidableEq

inductive BExpr : Type where
  /-- b1 = b2 -/
  | beq (b1 b2: BVal)
  /-- b1 < b2 -/
  | blt (e1 e2: BVal)
  /-- b1 <= b2 -/
  | ble (e1 e2: BVal)
  /-- e1 /\ e2 -/
  | band (e1 e2: BExpr)
  /-- not e -/
  | bnot (e: BExpr)
deriving Inhabited, Repr, DecidableEq

inductive BMonoTy : Type where
  /-- Type variable. -/
  | ftvar (name : TyIdentifier)
  /-- Type constructor. -/
  | tcons (name : String) (args : List BMonoTy)
  /-- Special support for bitvector types of every size. -/
  | bitvec (size : Nat)
  /-- Added to LMonoTy: bounded ints -/
  | boundint (b: BExpr)
deriving Inhabited, Repr

-- When desugaring to Lambda types, all bounded ints are erased
def BMonoTy_to_LMonoTy (b: BMonoTy) : Lambda.LMonoTy :=
  match b with
  | .ftvar name => Lambda.LMonoTy.ftvar name
  | .tcons name args => Lambda.LMonoTy.tcons name (List.map BMonoTy_to_LMonoTy args)
  | .bitvec size => Lambda.LMonoTy.bitvec size
  | .boundint _ => Lambda.LMonoTy.int

end Bounded
