/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.ListUtils
public import Strata.Languages.Core.ProgramType
public import Strata.Languages.Core.WF
public import Strata.Languages.Core.StatementWF
public import Strata.Languages.Core.ProcedureWF
import all Strata.Languages.Core.Program
import all Strata.Languages.Core.ProgramType
import all Strata.Languages.Core.StatementType

/-! ## Well-Formedness for Programs
  This file is the entry point of typechecker correctness proofs. Specifically,
 `Program.typeCheckWF` states that if a program successfully type checks,
 then it is also well-formed.

 Currently, the following properties are left admitted, but eventually the type
 checker should be updated to check all WF conditions defined in `WF.lean`, and
 the admitted goals should be discharged by their corresponding proofs. Here is
 a list of the properties admitted, and they are also documented in the proof
 next to the admit/sorry tactic.

 1. All local variable declarations in a procedure have no duplicates.
 2. The `lhs` of a call statement contain no duplicates.
 3. The `outputs` list of a procedure contains no duplicates
 4. The `inputs` list of a procedure contains no duplicates
 5. All variables in pre/post conditions must be in `outputs` or `inputs` of the procedure

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

public section

/- The default program is well-formed -/
theorem Program.init.wf : WFProgramProp .init where
  namesNodup := by
   simp [Program.init, Program.getNames, Program.getNames.go]
  wfdecls := by
    unfold WFDeclsProp
    simp [Program.init]

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


private theorem Program.find?.go_none_of_append : Program.find?.go kind name (acc1 ++ acc2) = none → Program.find?.go kind name acc1 = none := by
  induction acc1 <;> simp [Program.find?.go]
  rename_i h t ind
  split <;> simp_all

private theorem Program.typeCheck.go_elim_acc:
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
  any_goals (rw [← List.cons_append]; intro; apply ind (by assumption))

@[grind →]
private theorem Program.typeCheckAux_elim_singleton: Program.typeCheck.go p C ds T [s] = Except.ok (pp, T') →
  Program.typeCheck.go p C ds T [] = Except.ok (pp.drop 1, T') := by
  intro H
  have : [s] = [] ++ [s] := by simp
  rw [this] at H; have H:=  Program.typeCheck.go_elim_acc H
  simp [H]

@[local simp, local grind =]
private theorem Except_ok_bind {E α β}
  (a : α) (h : α → Except E β) :
  (.ok a >>= h) = h a := by
  simp [bind, Except.bind]

@[local simp, local grind =]
private theorem Except_error_bind {E α β}
  (e : E) (h : α → Except E β) :
  (.error e >>= h) = .error e := by
  simp [bind, Except.bind]

private theorem Except_bind_is_ok {E α β}
  (m : Except E α) (h : α → Except E β) (r : β) :
  ((m >>= h) = .ok r) ↔ ∃(a : α), m = .ok a ∧ h a = .ok r := by
  match m with
  | .ok a => grind
  | .error e => grind

@[local grind →]
private theorem Except_bind_is_ok_rhs {E α β}
  (m : Except E α) (h : α → Except E β) (r : β) :
  ((m >>= h) = .ok r) → ∃(a : α), m = .ok a ∧ h a = .ok r :=
  Except_bind_is_ok m h r |>.mp

@[local grind .]
private theorem WFTypeDeclarationProp_trivial (p : Program) (f : TypeDecl) :
  WFTypeDeclarationProp p f := by
  constructor

@[local grind .]
private theorem WFAxiomDeclarationProp_trivial (p : Program) (f : Axiom) :
  WFAxiomDeclarationProp p f := by
  constructor

@[local grind .]
private theorem WFDistinctDeclarationProp_trivial (p : Program) (l : Expression.Ident) (es : List (Expression.Expr)) :
  WFDistinctDeclarationProp p l es := by
  constructor

@[local grind .]
private theorem WFFunctionProp_trivial (p : Program) (f : Function) :
  WFFunctionProp p f := by
  constructor

private theorem List.foldlM_error_conditional (f: α → Bool) (g: α → β) (l: List α):
  List.foldlM (fun _ x =>
    if f x then Except.error (g x)
    else Except.ok ()) () l = Except.ok x →
  ∀ y, y ∈ l → ¬ (f y) := by
  induction l generalizing x <;> grind

/-
attribute [local grind .] Procedure.typeCheckWF

/--
Auxiliary lemma for Program.typeCheckWF
-/
private theorem Program.typeCheck.goWF : Program.typeCheck.go p C T ds [] = .ok (ds', T') → WF.WFDeclsProp p ds := by
  intros tcok
  induction ds generalizing ds' C T T' with
  | nil => simp
  | cons h t hyp =>
    simp only [Program.typeCheck.go, Except_bind_is_ok] at tcok
    let ⟨idents, ⟨ident_eq, q⟩⟩ := tcok
    clear tcok
    match h with
    | Decl.type td md =>
      grind
    | .ax a _ =>
      grind
    | .distinct l es md =>
      grind
    | .proc proc md =>
      grind
    | .func func md =>
      grind
    | .recFuncBlock funcs md =>
      simp only [] at q
      split at q
      -- First contradiction: empty funcs list
      case isTrue =>
        simp [Except_bind_is_ok, tryCatch, tryCatchThe, MonadExceptOf.tryCatch] at q
        rcases q with ⟨x, ⟨y, ⟨z, ⟨hcon, _⟩⟩⟩⟩
        contradiction
      simp only [Except_bind_is_ok] at q
      rcases q with ⟨res, ⟨q, hty⟩⟩
      simp only [Except.tryCatch, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.bind, bind, pure, Except.pure] at q
      split at q <;> try contradiction
      cases q
      rename_i q
      split at q <;> try contradiction
      rename_i hinline_poly
      split at q <;> try contradiction
      rename_i htypecheck
      cases q; simp at hty
      -- Get info about inline, no poly, no dups
      have hin:= List.foldlM_error_conditional _ _ _ hinline_poly
      have hnodup := Identifiers.addListWithErrorNoDup ident_eq
      simp only[Decl.names] at hnodup
      unfold WFDeclsProp
      refine (List.Forall_cons (WFDeclProp p) (Decl.recFuncBlock funcs md) t).mpr ?_
      constructor
      case right => grind
      case left =>
        simp only [WFDeclProp]
        constructor <;> grind
-/

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

private theorem addFactoryFunction_idents {T : LExprParams} (C : LContext T) (fn : LFunc T) :
    (C.addFactoryFunction fn).idents = C.idents := by
  simp [LContext.addFactoryFunction]
  if h : fn.name.name ∈ C.functions then
    simp [h]
  else
    simp [h]

/-- `List.foldl addFactoryFunction` does not change `idents`. -/
private theorem foldl_addFactoryFunction_idents {T : LExprParams} {C : LContext T} {fs : List α} {g : α → LFunc T} :
    (fs.foldl (fun C f => C.addFactoryFunction (g f)) (init := C)).idents = C.idents := by
  induction fs generalizing C with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.foldl, ih, addFactoryFunction_idents]

/-- If `Except.mapError` returns `.ok`, then the underlying result was also `.ok`. -/
private theorem Except.mapError_ok {α β γ} {f : α → β} {e : Except α γ} {v : γ} :
    Except.mapError f e = .ok v → e = .ok v := by
  cases e with
  | error _ => simp [Except.mapError]
  | ok val => simp [Except.mapError]

/--
If a program typechecks successfully, then every identifier in the list of
program decls is not in the original `LContext`
-/
private theorem Program.typeCheckFunctionDisjoint :
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
      split at Hty <;> try contradiction
      simp only[pure, Except.pure] at Hty
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
    | recFuncBlock fs =>
      split_contra_case Hty; rename_i Hty
      split at Hty <;> try contradiction
      simp only[pure, Except.pure] at Hty
      split at Hty <;> try contradiction
      split at Hty <;> try contradiction
      cases Hty; simp at tcok
      rename_i Heq
      specialize (IH tcok)
      match hx with
      | Or.inl hx =>
        have Hnotin := (Identifiers.addListWithErrorNotin Hid x)
        simp [Decl.names] at *; grind
      | Or.inr (Exists.intro a (And.intro a_in x_in)) =>
        have Hcontains := Identifiers.addListWithErrorContains Hid x
        specialize a_in' tcok a_in x_in
        have a_notin := IH x a_in'
        rw[foldl_addFactoryFunction_idents] at a_notin
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
private theorem Program.typeCheckFunctionNoDup : Program.typeCheck.go p C T decls acc = .ok (d', T') → (Program.getNames.go decls).Nodup := by
  induction decls generalizing acc p C T with
  | nil => simp[Program.getNames.go]
  | cons r rs IH =>
    simp[Program.getNames.go, Program.typeCheck.go, bind, Except.bind,
         tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch]
    split <;> try (intros;contradiction)
    rename_i x v Hid
    cases r with (simp only[]; intros tcok <;> split_contra tcok <;> simp only [Decl.names] at Hid <;> rename_i Hty)
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
      split at Hty <;> try contradiction
      simp only[pure, Except.pure] at Hty
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
    | recFuncBlock fs =>
      split_contra_case Hty; rename_i Hty
      split at Hty <;> try contradiction
      simp only[pure, Except.pure] at Hty
      split at Hty <;> try contradiction
      split at Hty <;> try contradiction
      cases Hty; simp at tcok
      specialize (IH tcok)
      apply List.nodup_append.mpr
      constructor; apply (Identifiers.addListWithErrorNoDup Hid)
      constructor; apply IH
      intros a a_in; simp[Decl.names] at a_in
      intros x x_in
      have Hdisj := Program.typeCheckFunctionDisjoint tcok _ x_in
      have x_contains := (Identifiers.addListWithErrorContains Hid x)
      rw [foldl_addFactoryFunction_idents] at Hdisj
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

/-
/--
The main lemma stating that a program 'p' that passes type checking is well formed
-/
theorem Program.typeCheckWF : Program.typeCheck C T p = .ok (p', T') → WF.WFProgramProp p := by
  intros tcok
  simp [Program.typeCheck, Except_bind_is_ok] at tcok
  let ⟨ds, ⟨tcOk, _⟩⟩ := tcok
  constructor
  case namesNodup =>
    exact typeCheckFunctionNoDup tcOk
  case wfdecls =>
    exact typeCheck.goWF tcOk
-/

end -- public section

end WF
end Core
