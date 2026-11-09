/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.AST
public import Strata.DL.Imperative.CmdSemantics

namespace Cortex

public section

open Imperative

@[expose] def mkRef (a : Nat) : Expr := .const () (.intConst a)

@[expose] def getRef? : Expr → Option Nat
  | .const _ (.intConst n) => if 0 ≤ n then some n.toNat else none
  | _ => none

structure Obj where
  type : TypeName
  fields : FieldRef → Option Expr

abbrev Heap := Nat → Option Obj

@[expose] def Heap.update (h : Heap) (a : Nat) (o : Obj) : Heap :=
  fun b => if b = a then some o else h b

@[expose] def Obj.setField (o : Obj) (r : FieldRef) (v : Expr) : Obj :=
  { o with fields := fun r' => if r' = r then some v else o.fields r' }

inductive Outcome where
  | normal
  | exn (v : Expr)

@[expose] def dynType (h : Heap) (v : Expr) : Option TypeName :=
  ((getRef? v).bind h).map (·.type)


end

end Cortex
