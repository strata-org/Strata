/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.ListUtils
import Strata.Languages.Core.ProgramType
import Strata.Languages.Core.WF
import Strata.Languages.Core.StatementWF
import Strata.Languages.Core.ProcedureWF

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
 2. All declared global variables are `CoreIdent.glob`.
 -  All local variable declarations in a procedure are `CoreIdent.locl`.
 4. All local variable declarations in a procedure have no duplicates.
 5. All variables in post-conditions and pre-conditions are either `CoreIdent.locl` or `CoreIdent.glob`.
 6. Postconditions in a procedure are all `ValidExpression`s (c.f., `OldExpressions.lean`),
    that is, the old predicates do not occur on the right hand side of an `.app`.
 7. The `lhs` of a call statement contain no duplicates and are `CoreIdent.locl`.
    This is to avoid overlapping with global variables that occurs in pre/post conditions, because call elimination directly substitutes `lhs` into the
    pre/post conditions, they must not already exist in the pre/post conditions.
    If a `lhs` needs to be global, a separate transformation can be implemented to create/substitute temporary variables before the call statement, and insert an assignment statement to
 +  The `outputs` list of a procedure contains no duplicates
 9. All variables mentioned in `args` of a call statement are either `CoreIdent.locl` or `CoreIdent.glob`.
 +  The `inputs` list of a procedure contains no duplicates
 11. All `modifies` variables have no duplicates.
 12. The `inputs` list of a procedure is disjoint from the `outputs` list of the procedure
 13. The `lhs` of a call statement is disjoint from `modifies`, `outputs`, and `inputs` of the procedure
 14. The `inputs` list of a procedure are all `CoreIdent.locl`
 15. The `outputs` list of a procedure are all `CoreIdent.locl`
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

namespace Core
namespace WF

open Imperative Std Lambda
open Strata

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
                  -- 2. All declared global variables are `CoreIdent.glob`.
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
            : TEnv CoreIdent } -- NOTE: this type annotation is important
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
  (Program.typeCheck.go p C T ds (acc1 ++ acc2) = Except.ok (pp, T') →
  (List.IsPrefix acc2.reverse pp ∧ Program.typeCheck.go p C T ds acc1 = Except.ok (pp.drop acc2.length, T')))
  := by
  induction ds generalizing pp acc1 C T
  simp [Program.typeCheck.go]
  intro  H
  simp [← H]
  rename_i h t ind
  simp [Program.typeCheck.go]
  simp [bind, Except.bind]
  split; intros; contradiction
  any_goals (split <;> try contradiction)
  any_goals (split <;> try (intros; contradiction))
  any_goals (split <;> try (intros; contradiction))
  any_goals (rw [← List.cons_append]; intro; apply ind (by assumption))

theorem Program.typeCheckAux_elim_singleton: Program.typeCheck.go p C ds T [s] = Except.ok (pp, T') →
  Program.typeCheck.go p C ds T [] = Except.ok (pp.drop 1, T') := by
  intro H
  have : [s] = [] ++ [s] := by simp
  rw [this] at H; have H:=  Program.typeCheck.go_elim_acc H
  simp [H]

/--
Auxiliary lemma for Program.typeCheckWF
-/
theorem Program.typeCheck.goWF : Program.typeCheck.go p C T ds [] = .ok (ds', T') → WF.WFDeclsProp p ds := by
  intros tcok
  induction ds generalizing ds' C T T' with
  | nil => simp [Program.typeCheck.go] at tcok
           cases tcok; constructor <;> try assumption
  | cons h t t_ih =>
    simp [Program.typeCheck.go, bind, Except.bind, tryCatch] at tcok
    split at tcok <;> try contradiction
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

-- Reasoning about unique identifiers

/--
`LContext.addKnownTypeWithError` does not change the set of known identifiers
-/
theorem addKnownTypeWithErrorIdents {C: Expression.TyContext}: C.addKnownTypeWithError kn f = .ok C' → C.idents = C'.idents := by
  unfold LContext.addKnownTypeWithError;
  simp[bind];
  cases t_eq: C.knownTypes.addWithError kn f
  case error => intros _; contradiction
  case ok k'=> simp[Except.bind]; intros T'; subst T'; rfl

theorem addMutualBlockIdents {C: Expression.TyContext} {m}: C.addMutualBlock m = .ok C' → C.idents = C'.idents := by
  unfold LContext.addMutualBlock;
  simp only[bind, Except.bind, pure, Except.pure];
  intros Hok
  repeat (split at Hok <;> try contradiction)
  grind

syntax "split_contra" ident : tactic
macro_rules
  | `(tactic|split_contra $t) =>
  `(tactic| split at $t:ident <;> (try contradiction))

syntax "split_contra_case" ident : tactic
macro_rules
  | `(tactic|split_contra_case $t) =>
  `(tactic| split at $t:ident <;> (try contradiction); cases $t:ident)

/-- If `Except.mapError` returns `.ok`, then the underlying result was also `.ok`. -/
theorem Except.mapError_ok {α β γ} {f : α → β} {e : Except α γ} {v : γ} :
    Except.mapError f e = .ok v → e = .ok v := by
  cases e with
  | error _ => simp [Except.mapError]
  | ok val => simp [Except.mapError]

/--
If a program typechecks successfully, then every identifier in the list of
program decls is not in the original `LContext`
-/
theorem Program.typeCheckFunctionDisjoint :
    Program.typeCheck.go p C T decls acc = .ok (d', T') →
    (∀ x, x ∈ Program.getNames.go decls → ¬ C.idents.contains x) := by
  induction decls generalizing acc p d' T' T C with
  | nil => simp[Program.getNames.go]
  | cons r rs IH =>
    simp[Program.getNames.go, Program.typeCheck.go, bind, Except.bind,
         tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch]
    split <;> try (intros;contradiction)
    rename_i x v Hid
    -- Need mem hypothesis in more useful form
    have a_in': ∀ {x1 x2 l d' T'},
      Program.typeCheck.go p x1 x2 rs l = .ok (d', T') →
      ∀ {x: CoreIdent} {a: Decl}, a ∈ rs → x ∈ a.names →
      x ∈ Program.getNames.go rs := by
      intros x1 x2 l d' T' Hty x a a_in x_in; unfold Program.getNames.go
      rw[List.mem_flatMap]; exists a
    cases r with (simp only[]; intros tcok <;> split_contra tcok <;> simp only [Decl.names] at Hid <;> rename_i Hty <;> intros x hx)
    | var v =>
      split_contra tcok
      specialize (IH tcok)
      match hx with
      | Or.inl hx =>
        have Hnotin:= (Identifiers.addListWithErrorNotin Hid x)
        simp [Decl.names, Decl.name] at *; subst_vars
        grind
      | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
        have Hcontains := Identifiers.addListWithErrorContains Hid x
        grind
    | ax a =>
      specialize (IH tcok)
      match hx with
      | Or.inl hx =>
        have Hnotin:= (Identifiers.addListWithErrorNotin Hid x)
        simp [Decl.names, Decl.name] at *; subst_vars
        grind
      | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
        have Hcontains := Identifiers.addListWithErrorContains Hid x
        grind
    | distinct d =>
      specialize (IH tcok)
      match hx with
      | Or.inl hx =>
        have Hnotin:= (Identifiers.addListWithErrorNotin Hid x)
        simp [Decl.names, Decl.name] at *; subst_vars
        grind
      | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
        have Hcontains := Identifiers.addListWithErrorContains Hid x
        grind
    | proc p =>
      specialize (IH tcok)
      match hx with
      | Or.inl hx =>
        have Hnotin:= (Identifiers.addListWithErrorNotin Hid x)
        simp [Decl.names, Decl.name] at *; subst_vars
        grind
      | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
        have Hcontains := Identifiers.addListWithErrorContains Hid x
        grind
    | func f =>
      split_contra_case Hty; rename_i Hty
      split_contra_case Hty; rename_i Hty
      specialize (IH tcok)
      match hx with
      | Or.inl hx =>
        have Hnotin:= (Identifiers.addListWithErrorNotin Hid x)
        simp [Decl.names, Decl.name] at *; subst_vars
        grind
      | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
        have Hcontains := Identifiers.addListWithErrorContains Hid x
        specialize a_in' tcok a_in x_in
        have a_notin := IH x a_in';
        simp only[LContext.addFactoryFunction] at a_notin
        grind
    | type t =>
      cases t with (simp only[] at Hty <;> split_contra_case Hty <;> rename_i Hty; split_contra Hty <;> rename_i Hty)
      | con c =>
        specialize (IH tcok)
        match hx with
        | Or.inl hx =>
          have Hnotin:= (Identifiers.addListWithErrorNotin Hid x)
          simp [Decl.names, Decl.name] at *; subst_vars
          grind
        | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
          have Hcontains := Identifiers.addListWithErrorContains Hid x
          have := addKnownTypeWithErrorIdents (by assumption)
          grind
      | syn s =>
        specialize (IH tcok)
        match hx with
        | Or.inl hx =>
          have Hnotin:= (Identifiers.addListWithErrorNotin Hid x)
          simp [Decl.names, Decl.name] at *; subst_vars
          grind
        | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
          have Hcontains := Identifiers.addListWithErrorContains Hid x
          grind
      | data d =>
        specialize (IH tcok)
        match hx with
        | Or.inl hx =>
          have Hnotin:= (Identifiers.addListWithErrorNotin Hid x)
          simp [Decl.names, Decl.name] at *; subst_vars
          grind
        | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
          have Hcontains := Identifiers.addListWithErrorContains Hid x
          split at Hty <;> simp_all
          have := addMutualBlockIdents (by assumption);
          grind

/--
If a program typechecks succesfully, all identifiers defined in the program are
unique.
-/
theorem Program.typeCheckFunctionNoDup : Program.typeCheck.go p C T decls acc = .ok (d', T') → (Program.getNames.go decls).Nodup := by
  induction decls generalizing acc p C T with
  | nil => simp[Program.getNames.go]
  | cons r rs IH =>
    simp[Program.getNames.go, Program.typeCheck.go, bind, Except.bind,
         tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch]
    split <;> try (intros;contradiction)
    rename_i x v Hid
    cases r with (simp only[]; intros tcok <;> split_contra tcok <;> simp only [Decl.names] at Hid <;> rename_i Hty)
    | var v =>
      split_contra tcok
      specialize (IH tcok)
      apply List.nodup_append.mpr; (repeat (constructor <;> try grind)); apply IH
      intros a a_in; simp[Decl.names] at a_in; subst_vars
      intros x x_in;
      have Hdisj:= Program.typeCheckFunctionDisjoint tcok _ x_in
      have x_contains := (Identifiers.addListWithErrorContains Hid x)
      simp_all; grind
    | ax a =>
      specialize (IH tcok)
      apply List.nodup_append.mpr; (repeat (constructor <;> try grind)); apply IH
      intros a a_in; simp[Decl.names] at a_in; subst_vars
      intros x x_in;
      have Hdisj:= Program.typeCheckFunctionDisjoint tcok _ x_in
      have x_contains := (Identifiers.addListWithErrorContains Hid x)
      simp_all; grind
    | distinct d =>
      specialize (IH tcok)
      apply List.nodup_append.mpr; (repeat (constructor <;> try grind)); apply IH
      intros a a_in; simp[Decl.names] at a_in; subst_vars
      intros x x_in;
      have Hdisj:= Program.typeCheckFunctionDisjoint tcok _ x_in
      have x_contains := (Identifiers.addListWithErrorContains Hid x)
      simp_all; grind
    | proc p =>
      specialize (IH tcok)
      apply List.nodup_append.mpr; (repeat (constructor <;> try grind)); apply IH
      intros a a_in; simp[Decl.names] at a_in; subst_vars
      intros x x_in;
      have Hdisj:= Program.typeCheckFunctionDisjoint tcok _ x_in
      have x_contains := (Identifiers.addListWithErrorContains Hid x)
      simp_all; grind
    | func f =>
      split_contra_case Hty; rename_i Hty
      split_contra_case Hty; rename_i Hty
      specialize (IH tcok)
      apply List.nodup_append.mpr; (repeat (constructor <;> try grind)); apply IH
      intros a a_in; simp[Decl.names] at a_in; subst_vars
      intros x x_in;
      have Hdisj:= Program.typeCheckFunctionDisjoint tcok _ x_in
      have x_contains := (Identifiers.addListWithErrorContains Hid x)
      simp_all
      simp[LContext.addFactoryFunction] at Hdisj
      grind
    | type td =>
      specialize (IH tcok)
      apply List.nodup_append.mpr
      cases td with (simp only[] at Hty <;> split_contra_case Hty <;> rename_i Hty <;> split_contra Hty <;> rename_i Hty)
      | con c =>
        constructor; simp[Decl.names, TypeDecl.names]; constructor; apply IH
        intros a a_in; simp[Decl.names, TypeDecl.names] at a_in; subst_vars
        intros x x_in;
        have Hdisj:= Program.typeCheckFunctionDisjoint tcok _ x_in
        have x_contains := (Identifiers.addListWithErrorContains Hid x)
        have := addKnownTypeWithErrorIdents (by assumption)
        simp_all[Decl.names, TypeDecl.names];
        grind
      | syn s =>
        constructor; simp[Decl.names, TypeDecl.names]; constructor; apply IH
        intros a a_in; simp[Decl.names, TypeDecl.names] at a_in; subst_vars
        intros x x_in;
        have Hdisj:= Program.typeCheckFunctionDisjoint tcok _ x_in
        have x_contains := (Identifiers.addListWithErrorContains Hid x)
        simp_all[Decl.names, TypeDecl.names];
        grind
      | data m =>
        -- mutual block has nodups
        constructor; apply (Identifiers.addListWithErrorNoDup Hid)
        constructor; apply IH
        intros a a_in; simp[Decl.names, TypeDecl.names] at a_in; subst_vars
        intros x x_in;
        have Hdisj:= Program.typeCheckFunctionDisjoint tcok _ x_in
        have x_contains := (Identifiers.addListWithErrorContains Hid x)
        simp_all[Decl.names, TypeDecl.names];
        split at Hty <;> simp_all
        have := addMutualBlockIdents (by assumption);
        grind

/--
The main lemma stating that a program 'p' that passes type checking is well formed
-/
theorem Program.typeCheckWF : Program.typeCheck C T p = .ok (p', T') → WF.WFProgramProp p := by
  intros tcok
  simp [Program.typeCheck] at tcok
  simp[bind, Except.bind] at tcok
  split at tcok; contradiction
  rename_i x v Hgo
  constructor; exact (Program.typeCheckFunctionNoDup Hgo)
  exact typeCheck.goWF Hgo

end WF
end Core
