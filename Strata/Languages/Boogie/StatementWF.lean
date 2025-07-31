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



import Strata.DL.Util.Props
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.WF
import Strata.Languages.Boogie.StatementType

---------------------------------------------------------------------
namespace Boogie
namespace WF

open Std Lambda

set_option warn.sorry false in
/--
A list of Statement 'ss' that passes type checking is well formed with respect to the whole program 'p'.
-/
theorem Statement.typeCheckWF :
  Statement.typeCheck T p proc ss = Except.ok (pp', T') →
  WF.WFStatementsProp p ss := by
  intros tcok
  simp only [Statement.typeCheck, bind, Except.bind] at *
  induction ss generalizing T pp' T' with
  | nil => constructor
  | cons h t ih =>
  apply (forall_cons (WF.WFStatementProp p) h t).mpr
  apply And.intro
  . unfold Statement.typeCheckAux at tcok
    simp only [bind] at tcok
    cases h with
    | cmd c =>
      cases c with
      | call lhs procName args md =>
        -- Show that the called procedure is declared
        simp [Except.bind, Statement.typeCheckCmd] at tcok
        split at tcok <;> simp_all
        next _ _ heq =>
        split at heq <;> try simp_all
        next Hcall =>
        split at Hcall <;> try simp_all
        split at Hcall <;> simp_all
        split at Hcall <;> try simp_all
        split at Hcall <;> try simp_all
        constructor <;> simp_all
      | cmd =>
        constructor
        -- 3. All local variable declarations in a procedure are `BoogieIdent.locl`.
        sorry
    | _ => constructor
    done
  . split at tcok <;> simp_all
    next Htc =>
    unfold Statement.typeCheckAux at Htc
    simp only [bind, Except.bind] at Htc
    cases h with
    | cmd c =>
      simp only at Htc
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      next Htc3 =>
      apply ih
      rw [Htc3]
    | block l b md =>
      simp at Htc
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      next Htc3 =>
      apply ih
      rw [Htc3]
    | ite c tb e md =>
      simp at Htc
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      next heq =>
      apply ih
      rw [heq]
    | loop g m i b md =>
      sorry
    | goto l =>
      simp at Htc
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      next heq =>
      apply ih
      rw [heq]

end WF
end Boogie
