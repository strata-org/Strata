/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
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
