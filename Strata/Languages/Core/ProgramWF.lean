/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DL.Lambda.IdentifiersProps

public import Strata.Languages.Core.ProgramType
public import Strata.Languages.Core.WF
import all Strata.Languages.Core.Program
import all Strata.Languages.Core.ProgramType
import all Strata.Languages.Core.StatementType
import all Strata.Languages.Core.TypeDecl
import all Strata.Languages.Core.RecFuncBlockType
import all Strata.DL.Lambda.LExprTypeEnv
import Strata.Languages.Core.Typing.Soundness.TypeDecl
import Strata.Languages.Core.Typing.Soundness.RecFuncBlockInversion
import Strata.Languages.Core.Typing.Props.FunctionTypeProps
import Strata.DL.Lambda.LExprTypeEnvProps
import Strata.Util.ExceptProps
import Strata.Util.Tactics
import Std.Do.Triple.SpecLemmas
import Std.Tactic.BVDecide.Normalize.Prop

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

/-- A walk started with the accumulator `acc1 ++ acc2` returns `acc2.reverse` followed by the
    output of the same walk started with `acc1`. -/
private theorem Program.typeCheck.goWith_elim_acc:
  (Program.typeCheck.goWith p PS S C T ds (acc1 ++ acc2) = Except.ok (pp, T') →
  (List.IsPrefix acc2.reverse pp ∧
    Program.typeCheck.goWith p PS S C T ds acc1 = Except.ok (pp.drop acc2.length, T')))
  := by
  induction ds generalizing pp acc1 S C T
  simp only [Program.typeCheck.goWith, List.reverse_append, Except.ok.injEq, Prod.mk.injEq,
    and_imp]
  intro  H
  simp [← H]
  rename_i h t ind
  simp only [Program.typeCheck.goWith, Program.typeCheck.stepThen]
  simp only [bind, Except.bind]
  iterate 3 (split; intros; contradiction)
  any_goals (split <;> try contradiction)
  any_goals (split <;> try (intros; contradiction))
  any_goals (rw [← List.cons_append]; intro; apply ind (by assumption))

@[grind →]
private theorem Program.typeCheckAux_elim_singleton:
  Program.typeCheck.go p C ds T [s] = Except.ok (pp, T') →
  Program.typeCheck.go p C ds T [] = Except.ok (pp.drop 1, T') := by
  intro hgo
  have hacc : [s] = [] ++ [s] := List.nil_append [s] |>.symm
  rw [hacc] at hgo
  exact (Program.typeCheck.goWith_elim_acc hgo).2

attribute [local simp, local grind =] Except.ok_bind Except.error_bind

@[local grind →]
private theorem Except_bind_is_ok_rhs {E α β}
  (m : Except E α) (h : α → Except E β) (r : β) :
  ((m >>= h) = .ok r) → ∃(a : α), m = .ok a ∧ h a = .ok r :=
  Except.bind_is_ok m h r |>.mp

@[local grind .]
private theorem WFTypeDeclarationProp_trivial (p : Program) (f : TypeDecl) :
  WFTypeDeclarationProp p f := by
  constructor

@[local grind .]
private theorem WFAxiomDeclarationProp_trivial (p : Program) (f : Axiom) :
  WFAxiomDeclarationProp p f := by
  constructor

@[local grind .]
private theorem WFDistinctDeclarationProp_trivial (p : Program) (l : Expression.Ident)
  (es : List (Expression.Expr)) :
  WFDistinctDeclarationProp p l es := by
  constructor

@[local grind .]
private theorem WFFunctionProp_trivial (p : Program) (f : Function) :
  WFFunctionProp p f := by
  constructor

/-
attribute [local grind .] Procedure.typeCheckWF

/--
Auxiliary lemma for Program.typeCheckWF
-/
private theorem Program.typeCheck.goWF :
    Program.typeCheck.go p C T ds [] = .ok (ds', T') → WF.WFDeclsProp p ds := by
  intros tcok
  induction ds generalizing ds' C T T' with
  | nil => simp
  | cons h t hyp =>
    simp only [Program.typeCheck.go, Except.bind_is_ok] at tcok
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
        simp [Except.bind_is_ok, tryCatch, tryCatchThe, MonadExceptOf.tryCatch] at q
        rcases q with ⟨x, ⟨y, ⟨z, ⟨hcon, _⟩⟩⟩⟩
        contradiction
      simp only [Except.bind_is_ok] at q
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
      have hin := fun y hy => (Except.ite_error_then_eq_ok.mp (foldlM_check_ok _ _ () hinline_poly y hy)).1
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
  simp only [bind];
  cases t_eq: C.knownTypes.addWithError kn f
  case error => intros _; contradiction
  case ok k'=> simp only [Except.bind, Except.ok.injEq]; intros T'; subst T'; rfl

/-- Checking an opaque type declaration leaves the known identifiers unchanged. -/
private theorem typeConstructorTypeCheckIdents {C: Expression.TyContext} {tc site Env}:
    TypeConstructor.typeCheck tc site C Env = .ok C' → C.idents = C'.idents :=
  fun h => addKnownTypeWithErrorIdents
    ((TypeConstructor.typeCheck_decompose tc site C C' Env h).2.2 default)

theorem addMutualBlockIdents {C: Expression.TyContext} {m}: C.addMutualBlock m = .ok C' → C.idents = C'.idents := by
  unfold LContext.addMutualBlock;
  simp only[bind, Except.bind, pure, Except.pure];
  intros Hok
  repeat (split at Hok <;> try contradiction)
  grind

/-- Checking a mutual datatype declaration leaves the known identifiers unchanged. -/
private theorem mutualDatatypeTypeCheckIdents {C : Expression.TyContext} {block Env r}
    (h : MutualDatatype.typeCheck block C Env = .ok r) : C.idents = r.2.1.idents := by
  unfold Core.MutualDatatype.typeCheck at h
  simp only [bind, Except.bind] at h
  repeat (split at h <;> try contradiction)
  cases h
  exact addMutualBlockIdents (by assumption)

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
  simp only [LContext.addFactoryFunction]
  if h : fn.name.name ∈ C.functions then
    simp [h]
  else
    simp [h]

/-- `List.foldl addFactoryFunction` does not change `idents`. -/
private theorem foldl_addFactoryFunction_idents {T : LExprParams} {C : LContext T}
    {fs : List α} {g : α → LFunc T} :
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

/-- Checking a recursive function block does not change the known identifiers. -/
private theorem RecFuncBlock.typeCheckIn_idents (S S' : Std.HashSet String)
    (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    C'.idents = C.idents := by
  obtain ⟨-, -, -, -, hC, -⟩ :=
    RecFuncBlock.typeCheckIn_decompose S S' C C' Env Env' funcs funcs' h
  rw [hC]
  unfold RecFuncBlock.fullContext
  exact foldl_addFactoryFunction_idents

/-- Inversion of an accepted declaration step at a function declaration, for any continuation
    `k`; the continuation runs in the unchanged environment, with the scope type-name set
    extended with the type names of the checked signature. -/
theorem Program.typeCheck.stepThen_func_inversion
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) (func : Function) (md : MetaData Expression) {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.func func md) k = .ok res) :
    ∃ (idents : Identifiers Unit) (renamed func' : Function),
      (∃ f, Identifiers.addListWithError i (Decl.func func md).names f = .ok idents)
      ∧ ¬ func.isRecursive
      ∧ func.name.name ∉ C.functions
      ∧ Function.typeCheckIn (Thunk.pure S)
          { C with idents := idents } Env.pushEmptySubstScope func = .ok (renamed, func')
      ∧ k (Decl.func func' md) { C.addFactoryFunction func'.toLFunc with idents := idents }
          Env (S.insertMany (funcSigTyNames func'.toLFunc)) = .ok res := by
  simp only [Program.typeCheck.stepThen, Decl.routePropBeforeRegistration, Decl.propCheck?,
    Decl.routeDistinctBeforeRegistration, bind, Except.bind, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  elim_err h with idents hidents
  elim_err h with resres hres
  elim_err hres with inner hinner
  simp only [Except.ok.injEq] at hres
  subst hres
  elim_err hinner with hnotrec
  elim_err hinner with hfresh
  elim_err hinner with tcres htc
  obtain ⟨renamed, func'⟩ := tcres
  simp only [Except.ok.injEq] at hinner
  subst hinner
  dsimp only [] at h
  rw [addFactoryFunction_setIdents] at h
  exact ⟨idents, renamed, func', ⟨_, hidents⟩, hnotrec,
    Function.checkNameFresh_ok (C := { C with idents := idents })
      (Except.mapError_ok_h' hfresh),
    Except.mapError_ok_h' htc, h⟩

/-- An accepted declaration step registers the declaration's names, and its continuation runs in a
    context whose identifiers are that registration. -/
private theorem Program.typeCheck.stepThen_idents {α : Type} (program : Program)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (decl : Decl)
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S C Env decl k = .ok res) :
    ∃ f idents d' C' Env' S', C.idents.addListWithError decl.names f = .ok idents
      ∧ C'.idents = idents ∧ k d' C' Env' S' = .ok res := by
  simp only [Program.typeCheck.stepThen, bind, Except.bind, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  elim_err h
  elim_err h
  elim_err h with idents hid
  split at h
  all_goals first
    | exact ⟨_, idents, _, _, _, _, hid, rfl, h⟩
    | (elim_err h with r hr
       refine ⟨_, idents, _, _, _, _, hid, ?_, h⟩)
  all_goals
    repeat (split_ns at hr <;> try contradiction)
  all_goals (try simp only [Except.ok.injEq] at hr)
  all_goals (try subst hr)
  all_goals (try rfl)
  all_goals
    rename_i hin
    repeat (split_ns at hin <;> try contradiction)
  all_goals (try simp only [Except.ok.injEq] at hin)
  all_goals (try subst hin)
  all_goals first
    | rfl
    | exact (typeConstructorTypeCheckIdents (by assumption)).symm
    | exact (mutualDatatypeTypeCheckIdents (by assumption)).symm
    | exact RecFuncBlock.typeCheckIn_idents _ _ _ _ _ _ _ _ (Except.mapError_ok (by assumption))
    | exact addFactoryFunction_idents _ _
    | (elim_err hin with v hv
       try simp only [Except.ok.injEq] at hin
       try subst hin
       first | rfl | exact (mutualDatatypeTypeCheckIdents hv).symm)

/-- A successful walk, with any type-name sets, declares no name that the identifiers of its
    starting context already contain. -/
private theorem Program.typeCheck.goWith_names_disjoint :
    Program.typeCheck.goWith p PS S C T decls acc = .ok (d', T') →
    (∀ x, x ∈ Program.getNames.go decls → ¬ C.idents.contains x) := by
  induction decls generalizing acc d' T' S T C with
  | nil => simp [Program.getNames.go]
  | cons r rs IH =>
    intro hgo x hx
    rw [Program.typeCheck.goWith] at hgo
    obtain ⟨_, idents, _, C2, _, _, Hid, hC2, tcok⟩ :=
      Program.typeCheck.stepThen_idents p C T r _ _ hgo
    rw [Program.getNames.go, List.flatMap_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [Identifiers.addListWithErrorNotin Hid x hx, Bool.false_eq_true,
        not_false_eq_true]
    · have hnot := IH tcok x hx
      rw [hC2, Identifiers.addListWithErrorContains Hid x] at hnot
      exact fun hC => hnot (Or.inr hC)

/-- A successful walk, with any type-name sets, declares no name twice. -/
private theorem Program.typeCheck.goWith_names_nodup :
    Program.typeCheck.goWith p PS S C T decls acc = .ok (d', T') →
    (Program.getNames.go decls).Nodup := by
  induction decls generalizing acc S C T with
  | nil => simp [Program.getNames.go]
  | cons r rs IH =>
    intro hgo
    rw [Program.typeCheck.goWith] at hgo
    obtain ⟨_, idents, _, C2, _, _, Hid, hC2, tcok⟩ :=
      Program.typeCheck.stepThen_idents p C T r _ _ hgo
    rw [Program.getNames.go, List.flatMap_cons]
    refine List.nodup_append.mpr ⟨Identifiers.addListWithErrorNoDup Hid, IH tcok, ?_⟩
    intro a ha b hb hab
    subst hab
    have hnot := Program.typeCheck.goWith_names_disjoint tcok a hb
    rw [hC2, Identifiers.addListWithErrorContains Hid a] at hnot
    exact hnot (Or.inl ha)

/-
/--
The main lemma stating that a program 'p' that passes type checking is well formed
-/
theorem Program.typeCheckWF : Program.typeCheck C T p = .ok (p', T') → WF.WFProgramProp p := by
  intros tcok
  simp [Program.typeCheck, Except.bind_is_ok] at tcok
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
