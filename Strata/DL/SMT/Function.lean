/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Term

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Function.lean)
This file defines an ADT that represents functions over terms.
-/

namespace Strata.SMT


inductive Function : Type where
  | uf : UF → Function
deriving instance Repr, DecidableEq, Inhabited for Function

def Function.argType (ff : Function) (i : Nat) : Option TermType :=
  match ff with
  | .uf f =>
    match f.args[i]? with
    | none => none
    | some arg => some arg.ty

def Function.outType : Function → TermType
  | .uf f => f.out

def Function.isUF : Function → Bool
  | .uf _ => true

end Strata.SMT
