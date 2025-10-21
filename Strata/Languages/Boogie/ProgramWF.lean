/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.ListUtils
import Strata.Languages.Boogie.ProgramType
import Strata.Languages.Boogie.WF
import Strata.Languages.Boogie.StatementWF
import Strata.Languages.Boogie.ProcedureWF

/-! ## Well-Formedness for Programs
  This file is the entry point of typechecker correctness proofs. Specifically,
 `Program.typeCheckWF` states that if a program successfully type checks,
 then it is also well-formed.

 Currently, the following properties are left admitted, but eventually the type
 checker should be updated to check all WF conditions defined in `WF.lean`, and
 the admitted goals should be discharged by their corresponding proofs. Here is
 a list of the properties admitted, and they are also documented in the proof
 next to the admit/sorry tactic. As proofs for the list items are completed, the
 number can be replaced with a '+' for documentation purposes. If a
 well-formedness condition is not needed, it is denoted by '-'.

 1. All `modifies` variables in a procedure are declared in the program.
 2. All declared global variables are `BoogieIdent.glob`.
 -  All local variable declarations in a procedure are `BoogieIdent.locl`.
 4. All local variable declarations in a procedure have no duplicates.
 5. All variables in post-conditions and pre-conditions are either `BoogieIdent.locl` or `BoogieIdent.glob`.
 6. Postconditions in a procedure are all `ValidExpression`s (c.f., `OldExpressions.lean`),
    that is, the old predicates do not occur on the right hand side of an `.app`.
 7. The `lhs` of a call statement contain no duplicates and are `BoogieIdent.locl`.
    This is to avoid overlapping with global variables that occurs in pre/post conditions, because call elimination directly substitutes `lhs` into the
    pre/post conditions, they must not already exist in the pre/post conditions.
    If a `lhs` needs to be global, a separate transformation can be implemented to create/substitute temporary variables before the call statement, and insert an assignment statement to
 +  The `outputs` list of a procedure contains no duplicates
 9. All variables mentioned in `args` of a call statement are either `BoogieIdent.locl` or `BoogieIdent.glob`.
 +  The `inputs` list of a procedure contains no duplicates
 11. All `modifies` variables have no duplicates.
 12. The `inputs` list of a procedure is disjoint from the `outputs` list of the procedure
 13. The `lhs` of a call statement is disjoint from `modifies`, `outputs`, and `inputs` of the procedure
 14. The `inputs` list of a procedure are all `BoogieIdent.locl`
 15. The `outputs` list of a procedure are all `BoogieIdent.locl`
 16. All variables in pre/post conditions that are `.locl` must be in `outputs` or `inputs` of the procedure

 In order to fully prove the type checker's properties, it might be necessary to
 establish a connection (currently not implemented) between the `TyEnv` instance
 that is passed to, or returned from, the type checker and the `Program`
 instance that is associated to the type-checking. Specifically, the following
 two theorems (phrased in plain words) can be helpful in establishing such a
 connection:

 Definition 1, WFTyEnvProgram (T : TyEnv) (p : Program): `WFTyEnv T p` means
 that, for all variables `v`, if `v` exists in the type environment `T`, then it
 must exist as a global variable of program `p`.

 Theorem 1, WFTyEnv_monotone : if `WFTyEnvProgram T p` holds, and type-checking
 for any sub-component of `p` succeeds in the context of program `p`, and
 returns a new `TyEnv` instance `T'` then `WFTyEnvProgram T' p` holds.

 All WF lemmas can be modified to take Theorem 1 as a premise, since an empty
 type environment always satisfy Property 1.

 Additionally, it might also be necessary to claim those properties on the
 _returned_ entity (e.g., a `Program`, a `Procedure`, etc.) of the type
 checker, instead of the one passed in as an argument, since the type checker might want to resolve variable scopes and add those annotations

 Given the above, we should be able to prove properties such as all old
 expressions occurring in the postconditions are declared as global variables,
 since the type checker ensures that they exist in the typing environment.  And
 consequently, we can prove the main theorem that a program is well-formed if
 the program is type-checked.
-/

namespace Boogie
namespace WF

open Imperative Std Lambda

/- The default program is well-formed -/
theorem Program.init.wf : WFProgramProp .init := by
  constructor <;> simp [Program.init, Program.getNames, Program.getNames.go]
  constructor

/- WFProgram is inhabited -/
instance : Inhabited WFProgram where
  default := {
    self := .init,
    prop := Program.init.wf
  }

instance : ToFormat WFProgram where
  format wfp := format wfp.self

/-
/--
Auxiliary lemma for Program.typeCheck.goWF
-/
theorem Program.typeCheck.goWF' :
    Program.typeCheck.go p T (d :: ds) acc = .ok (ds', T') →
    WF.WFDeclProp p d ∧
    ∃ ds'' TT TT' , Program.typeCheck.go p TT ds acc' = .ok (ds'', TT') := by
  intros tcok
  simp only [Program.typeCheck.go] at tcok
  cases Hd: d with
  | var name ty e =>
    simp [Hd, Except.bind, bind, Statement.typeCheck] at tcok
    generalize Hinit : Statement.init name ty e = init at tcok
    cases Heq: Statement.typeCheckAux T p .none [Statement.init name ty e] with
    | error _ => simp_all
    | ok res =>
      simp_all
      cases Heq2: Statement.Statement.subst.go res.snd.state.substInfo.subst res.fst with
      | nil => simp_all
      | cons h t =>
        simp_all
        cases Hh: h with
        | cmd c =>
          simp_all
          cases c with
          | cmd c =>
            cases c with
            | init id ty' e' md =>
              cases t with
              | cons _ _ => simp_all
              | nil =>
              simp_all
              split at tcok <;> simp_all
              next x v Heq3 =>
              simp [Hd] at *
              cases tcok with
              | intro l r =>
                apply And.intro
                . constructor
                  -- 2. All declared global variables are `BoogieIdent.glob`.
                  sorry
                . exists v.1, {
                  context := res.snd.context.subst res.snd.state.substInfo.subst,
                  state := res.snd.state, functions := res.snd.functions,
                  knownTypes := res.snd.knownTypes }, v.2
            | _ => simp_all
          | call _ => simp_all
        | _ => simp_all
  | type t =>
    simp [Hd, Except.bind, bind] at tcok
    apply And.intro
    . constructor
    . split at tcok
      . next td tc =>
        generalize HTT: (Lambda.TEnv.addKnownType T tc.toType) = TT
        cases H : Program.typeCheck.go p TT ds with
        | error _ => simp_all
        | ok res =>
          exists res.1, TT, res.2
      . split at tcok <;> simp_all; next td ts =>
        split at tcok <;> simp_all; next h =>
        split at tcok <;> try simp_all
        next mtys lhs rhs heq =>
        split at tcok <;> try simp_all
        next x v heq' =>
        split at tcok <;> try simp_all
        next x' v' Htc =>
        generalize Htys :
          (LMonoTys.instantiate td.typeArgs [td.toLHSLMonoTy, td.type] T).snd.context.types
          = tys at Htc
        generalize Hals :
          { args := lhs.freeVars, lhs := lhs, rhs := v.fst } ::
              (LMonoTys.instantiate td.typeArgs [td.toLHSLMonoTy, td.type] T).snd.context.aliases
          = aliases at Htc
        generalize HTT :
          { context := { types := tys, aliases := aliases },
            state := (LMonoTys.instantiate td.typeArgs [td.toLHSLMonoTy, td.type] T).snd.state,
            functions := (LMonoTys.instantiate td.typeArgs [td.toLHSLMonoTy, td.type] T).snd.functions,
            knownTypes := (LMonoTys.instantiate td.typeArgs [td.toLHSLMonoTy, td.type] T).snd.knownTypes
            : TEnv BoogieIdent } -- NOTE: this type annotation is important
          = TT at Htc
        exists v'.fst, TT, v'.snd
  | ax a =>
    simp only [Hd, Except.bind, bind] at tcok
    split at tcok <;> simp_all
    apply And.intro
    . constructor
    . split at tcok <;> try simp_all
      split at tcok <;> try simp_all
      next heq =>
      refine ⟨_, _, _, heq⟩
  | proc p' =>
    simp only [Hd, Except.bind, bind] at tcok
    generalize Htc : Procedure.typeCheck T p p' = tc at tcok
    cases tc with
    | error _ => simp_all
    | ok res =>
    apply And.intro
    . simp only at tcok
      exact Procedure.typeCheckWF Htc
    . cases res with
    | mk fst snd =>
      simp at tcok
      split at tcok <;> simp_all
      next x v heq =>
      exists v.1, snd, v.2
  | func f =>
    simp [Hd, Except.bind, bind] at tcok
    apply And.intro
    . constructor
    . cases H: Function.typeCheck T f with
      | error _ => simp_all
      | ok res =>
        cases res with
        | mk fst snd =>
          simp [H] at tcok
          split at tcok <;> simp_all
          next heq =>
          refine ⟨_, _, _, heq⟩
-/


theorem Program.find?.go_none_of_append : Program.find?.go kind name (acc1 ++ acc2) = none → Program.find?.go kind name acc1 = none := by
  induction acc1 <;> simp [Program.find?.go]
  rename_i h t ind
  split <;> simp_all

theorem Program.typeCheck.go_elim_acc:
  (Program.typeCheck.go p T ds (acc1 ++ acc2) = Except.ok (pp, T') →
  (List.IsPrefix acc2.reverse pp ∧ Program.typeCheck.go p T ds acc1 = Except.ok (pp.drop acc2.length, T')))
  := by
  induction ds generalizing pp acc1 T
  simp [Program.typeCheck.go]
  intro  H
  simp [← H]
  rename_i h t ind
  simp [Program.typeCheck.go]
  simp [bind, Except.bind]
  split <;> try contradiction
  any_goals (split <;> try contradiction)
  any_goals (split <;> try contradiction)
  any_goals (split <;> try contradiction)
  any_goals (split <;> try contradiction)
  any_goals (split <;> try contradiction)
  any_goals simp
  any_goals (rw [← List.cons_append]; intro; apply ind (by assumption))
  any_goals (rename_i H _ _ _ _; have H:= Program.find?.go_none_of_append H; simp_all)
  rename_i H _ _ _ _ _ _ _; have H:= Program.find?.go_none_of_append H; simp_all

theorem Program.typeCheckAux_elim_singleton: Program.typeCheck.go p ds T [s] = Except.ok (pp, T') →
  Program.typeCheck.go p ds T [] = Except.ok (pp.drop 1, T') := by
  intro H
  have : [s] = [] ++ [s] := by simp
  rw [this] at H; have H:=  Program.typeCheck.go_elim_acc H
  simp [H]

/--
Auxiliary lemma for Program.typeCheckWF
-/
theorem Program.typeCheck.goWF : Program.typeCheck.go p T ds [] = .ok (ds', T') → WF.WFDeclsProp p ds := by
  intros tcok
  induction ds generalizing ds' T T' with
  | nil => simp [Program.typeCheck.go] at tcok
           cases tcok; constructor <;> try assumption
  | cons h t t_ih =>
    simp [Program.typeCheck.go, bind, Except.bind] at tcok
    split at tcok <;> try contradiction
    any_goals (split at tcok <;> try contradiction)
    any_goals (split at tcok <;> try contradiction)
    any_goals (split at tcok <;> try contradiction)
    any_goals (split at tcok <;> try contradiction)
    simp
    any_goals simp [t_ih $ Program.typeCheckAux_elim_singleton tcok]
    have := Statement.typeCheckWF (by assumption)
    constructor
    simp [WFCmdExtProp] at this
    sorry
    any_goals (apply Procedure.typeCheckWF (by assumption))
    any_goals constructor

/--
The main lemma stating that a program 'p' that passes type checking is well formed
-/
theorem Program.typeCheckWF : Program.typeCheck T p = .ok (p', T') → WF.WFProgramProp p := by
  intros tcok
  simp [Program.typeCheck] at tcok
  cases (List.nodupDecidable (p.getNames DeclKind.var)) with
  | isFalse pvar => rw [if_neg pvar] at tcok ; cases tcok
  | isTrue pvar =>
    cases (List.nodupDecidable (p.getNames DeclKind.proc)) with
    | isFalse pproc => rw [if_pos pvar, if_neg pproc] at tcok ; cases tcok
    | isTrue pproc =>
      cases (List.nodupDecidable (p.getNames DeclKind.func)) with
      | isFalse pfunc => rw [if_pos pvar, if_pos pproc, if_neg pfunc] at tcok ; cases tcok
      | isTrue pfunc =>
        constructor <;> try assumption
        rw [if_pos pvar, if_pos pproc, if_pos pfunc] at tcok
        simp [bind, Except.bind] at tcok
        cases Hgo : Program.typeCheck.go p (TEnv.updateSubst T { subst := [[]], isWF := SubstWF_of_empty_empty }) p.decls [] with
        | error _ => simp_all
        | ok res => exact typeCheck.goWF Hgo

end WF
end Boogie
