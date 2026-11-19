/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.OperationalSemanticsProps
import all Strata.DL.Lambda.TypeFactoryWF
import all Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.LTy
public import Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.LTyUnifyProps

public import Strata.DL.Lambda.TypeFactory
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.TypeFactoryWF
public import Strata.DL.Lambda.FactoryWF

/-!
## Typing Assumptions

Collects all well-formedness and typing assumptions used by the denotational
semantics proofs. Semantic (denotation-level) assumptions live in
`LExprSemanticsConsistent`.

### Expression-level predicates
- `fvars_annotated_by` — free variable annotations match a type map; holds for
  `LExpr.resolve`'s output (`resolve_fvars_annotated_by`)
- `OpsConsistent` — operator type annotations are valid factory instantiations
  (TODO: prove satisfied after `LExpr.resolve`)
- `OpsConsistentR` — declarative form: some substitution turns each operator's generic type
  into its annotation (checked by `LExpr.opsConsistent`, `opsConsistent_sound`);
  holds for `LExpr.resolve`'s output (`resolve_opsConsistentR`)

### Factory assumptions (TODO: prove satisfied after `Function.typeCheck`)
- `Factory.WellTyped` / `Factory.EvalWellTyped` — bodies and evaluators preserve typing
- `Factory.ConstrWellFormed` — constructor functions match the type factory
- `Factory.BodyOpsConsistent` / `Factory.EvalOpsConsistent` — bodies and evaluators preserve `OpsConsistent`
- `Factory.BodyAnnotated` / `Factory.EvalAnnotated` — bodies and evaluators preserve annotations

### Environment assumptions (TODO: prove satisfied by `Program.typeCheck`)
- `Env.Typed` — environment values are well-typed

### Bundled assumptions
- `Env.StepWF` — environment well-formedness for step preservation
- `Factory.StepWF` — factory well-formedness for step preservation
- `Factory.WF` — factory and type-factory well-formedness

### Intro lemmas
The intro lemmas (`fvars_annotated_by.fvar`, `OpsConsistent.op_in`,
`Factory.WellTyped.intro`, …) live here, next to the definitions, because callers outside this
module discharge the definitions through them while the bodies stay hidden.
-/

namespace Lambda

variable {T : LExprParams} [DecidableEq T.IDMeta]

/-! ### Expression-level predicates -/

/-- Every fvar in `e` whose name is in `tyMap` is annotated with the
corresponding type. -/
public def fvars_annotated_by [DecidableEq T.IDMeta]
    (tyMap : Map T.Identifier LMonoTy) : LExpr T.mono → Prop
  | .fvar _ name (some ty) =>
    ∀ ty', Map.find? tyMap name = some ty' → ty = ty'
  | .fvar _ _ none => False
  | .const _ _ => True
  | .bvar _ _ => True
  | .op _ _ _ => True
  | .app _ fn arg => fvars_annotated_by tyMap fn ∧ fvars_annotated_by tyMap arg
  | .abs _ _ _ body => fvars_annotated_by tyMap body
  | .ite _ c t e => fvars_annotated_by tyMap c ∧ fvars_annotated_by tyMap t ∧ fvars_annotated_by tyMap e
  | .eq _ e1 e2 => fvars_annotated_by tyMap e1 ∧ fvars_annotated_by tyMap e2
  | .quant _ _ _ _ tr body => fvars_annotated_by tyMap tr ∧ fvars_annotated_by tyMap body

/-! Intro lemmas for `fvars_annotated_by`, one per clause a caller outside this module needs. -/

omit [DecidableEq T.IDMeta] in
/-- A free variable is annotated by `tyMap` when its annotation is every type `tyMap` gives its
    name. -/
public theorem fvars_annotated_by.fvar [DecidableEq T.IDMeta] {tyMap : Map T.Identifier LMonoTy}
    {m name ty} (h : ∀ ty', Map.find? tyMap name = some ty' → ty = ty') :
    fvars_annotated_by tyMap (.fvar m name (some ty)) := h

omit [DecidableEq T.IDMeta] in
/-- A constant is annotated by any type map. -/
public theorem fvars_annotated_by.const [DecidableEq T.IDMeta]
    {tyMap : Map T.Identifier LMonoTy} {m c} :
    fvars_annotated_by (T := T) tyMap (.const m c) := trivial

omit [DecidableEq T.IDMeta] in
/-- An operator is annotated by any type map. -/
public theorem fvars_annotated_by.op [DecidableEq T.IDMeta] {tyMap : Map T.Identifier LMonoTy}
    {m o ty} : fvars_annotated_by (T := T) tyMap (.op m o ty) := trivial

omit [DecidableEq T.IDMeta] in
/-- An application is annotated by `tyMap` when its function and argument are. -/
public theorem fvars_annotated_by.app [DecidableEq T.IDMeta] {tyMap : Map T.Identifier LMonoTy}
    {m fn arg} (hfn : fvars_annotated_by tyMap fn) (harg : fvars_annotated_by tyMap arg) :
    fvars_annotated_by (T := T) tyMap (.app m fn arg) := ⟨hfn, harg⟩

/-- Every `.op` node in `e` whose name is in the factory has a type annotation
that is a valid instantiation of the function's generic type (via `opTypeSubst`).
This is checked at every `.op` node directly, not just at complete calls. -/
public def OpsConsistent (F : @Factory T) : LExpr T.mono → Prop := fun e =>
  match e with
  | .op _ name ty =>
      match F[name.name]? with
      | some fn =>
          match LFunc.opTypeSubst fn e with
          | some tySubst =>
              match ty with
              | some ty_op =>
                  ty_op = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst tySubst
              | none => False
          | none => False
      | none => True
  | .app _ fn arg => OpsConsistent F fn ∧ OpsConsistent F arg
  | .abs _ _ _ body => OpsConsistent F body
  | .ite _ c t f => OpsConsistent F c ∧ OpsConsistent F t ∧ OpsConsistent F f
  | .eq _ e1 e2 => OpsConsistent F e1 ∧ OpsConsistent F e2
  | .quant _ _ _ _ tr body => OpsConsistent F tr ∧ OpsConsistent F body
  | _ => True

/-! Intro lemmas for `OpsConsistent`, one per clause a caller outside this module needs. -/

omit [DecidableEq T.IDMeta] in
/-- An operator the factory resolves, annotated at the instance `opTypeSubst` finds. -/
public theorem OpsConsistent.op_in {F : @Factory T} {m name ty_op fn tySubst}
    (hfn : F[name.name]? = some fn)
    (hsubst : LFunc.opTypeSubst fn (.op m name (some ty_op)) = some tySubst)
    (hty : ty_op = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst tySubst) :
    OpsConsistent F (.op m name (some ty_op)) := by
  unfold OpsConsistent; simp only [hfn, hsubst]; exact hty

omit [DecidableEq T.IDMeta] in
/-- A constant is consistent with any factory. -/
public theorem OpsConsistent.const {F : @Factory T} {m c} : OpsConsistent F (.const m c) :=
  by unfold OpsConsistent; trivial

omit [DecidableEq T.IDMeta] in
/-- A free variable is consistent with any factory. -/
public theorem OpsConsistent.fvar {F : @Factory T} {m x ty} : OpsConsistent F (.fvar m x ty) :=
  by unfold OpsConsistent; trivial

omit [DecidableEq T.IDMeta] in
/-- An application is consistent with `F` when its function and argument are. -/
public theorem OpsConsistent.app {F : @Factory T} {m fn arg} (hfn : OpsConsistent F fn)
    (harg : OpsConsistent F arg) : OpsConsistent F (.app m fn arg) := by
  unfold OpsConsistent; exact ⟨hfn, harg⟩

/-- Declarative form of `OpsConsistent` as an inductive relation. The `.op` case
requires that *some* type substitution turns the function's generic type into the
node's annotation; operators not in the factory are unconstrained. -/
public inductive OpsConsistentR (F : @Factory T) : LExpr T.mono → Prop where
  | const {m c} : OpsConsistentR F (.const m c)
  | bvar {m i} : OpsConsistentR F (.bvar m i)
  | fvar {m name ty} : OpsConsistentR F (.fvar m name ty)
  | op_notin {m name ty} (h : F[name.name]? = none) : OpsConsistentR F (.op m name ty)
  | op_in {m name ty_op fn tySubst}
      (hfn : F[name.name]? = some fn)
      (hty : ty_op = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst tySubst) :
      OpsConsistentR F (.op m name (some ty_op))
  | app {m fn arg} :
      OpsConsistentR F fn → OpsConsistentR F arg → OpsConsistentR F (.app m fn arg)
  | abs {m name ty body} : OpsConsistentR F body → OpsConsistentR F (.abs m name ty body)
  | ite {m c t f} :
      OpsConsistentR F c → OpsConsistentR F t → OpsConsistentR F f →
      OpsConsistentR F (.ite m c t f)
  | eq {m e1 e2} :
      OpsConsistentR F e1 → OpsConsistentR F e2 → OpsConsistentR F (.eq m e1 e2)
  | quant {m k name ty tr body} :
      OpsConsistentR F tr → OpsConsistentR F body →
      OpsConsistentR F (.quant m k name ty tr body)

section OpsConsistentRInversion
omit [DecidableEq T.IDMeta]
variable {F : @Factory T}

/-- Operator consistency at an application is operator consistency of the
    function and of the argument. -/
theorem OpsConsistentR.app_inv {m : T.Metadata} {fn arg : LExpr T.mono}
    (h : OpsConsistentR F (.app m fn arg)) :
    OpsConsistentR F fn ∧ OpsConsistentR F arg := by
  cases h with
  | app hf ha => exact ⟨hf, ha⟩

/-- Operator consistency of an abstraction gives that of its body. -/
theorem OpsConsistentR.abs_inv {m : T.Metadata} {name : String}
    {ty : Option LMonoTy} {body : LExpr T.mono}
    (h : OpsConsistentR F (.abs m name ty body)) :
    OpsConsistentR F body := by
  cases h with
  | abs hb => exact hb

/-- Operator consistency at a quantifier is operator consistency of its trigger
    and of its body. -/
theorem OpsConsistentR.quant_inv {m : T.Metadata} {k : QuantifierKind}
    {name : String} {ty : Option LMonoTy} {tr body : LExpr T.mono}
    (h : OpsConsistentR F (.quant m k name ty tr body)) :
    OpsConsistentR F tr ∧ OpsConsistentR F body := by
  cases h with
  | quant htr hb => exact ⟨htr, hb⟩

/-- Operator consistency at a conditional is operator consistency of the test
    and both branches. -/
theorem OpsConsistentR.ite_inv {m : T.Metadata} {c t f : LExpr T.mono}
    (h : OpsConsistentR F (.ite m c t f)) :
    OpsConsistentR F c ∧ OpsConsistentR F t ∧ OpsConsistentR F f := by
  cases h with
  | ite hc ht hf => exact ⟨hc, ht, hf⟩

/-- Operator consistency of an equality gives that of both sides. -/
theorem OpsConsistentR.eq_inv {m : T.Metadata} {e1 e2 : LExpr T.mono}
    (h : OpsConsistentR F (.eq m e1 e2)) :
    OpsConsistentR F e1 ∧ OpsConsistentR F e2 := by
  cases h with
  | eq h1 h2 => exact ⟨h1, h2⟩

/-- At an annotated operator the factory declares, operator consistency exhibits
    a substitution sending the declared arrow type to the annotation. -/
theorem OpsConsistentR.op_inv_of_declared {m : T.Metadata}
    {o : Identifier T.IDMeta} {f : LFunc T} {ty : LMonoTy}
    (hfind : F[o.name]? = some f) (h : OpsConsistentR F (.op m o (some ty))) :
    ∃ tySubst : Subst,
      ty = LMonoTy.subst tySubst
        (LMonoTy.mkArrow' f.output (List.map Prod.snd f.inputs)) := by
  cases h with
  | op_notin hnone =>
    rw [hfind] at hnone
    exact nomatch hnone
  | op_in hfn hty =>
    rename_i fn tySubst
    have hfneq : fn = f := by
      rw [hfn] at hfind
      exact Option.some_inj.mp hfind
    subst hfneq
    exact ⟨tySubst, hty⟩

end OpsConsistentRInversion

omit [DecidableEq T.IDMeta] in
/-- Soundness: `OpsConsistent` implies `OpsConsistentR`, using the substitution
from `opTypeSubst` as the `.op` witness. -/
theorem OpsConsistent_OpsConsistentR {F : @Factory T} :
    ∀ {e : LExpr T.mono}, OpsConsistent F e → OpsConsistentR F e := by
  intro e
  induction e with
  | const m c => intro _; exact .const
  | bvar m i => intro _; exact .bvar
  | fvar m name ty => intro _; exact .fvar
  | op m name ty =>
    intro h
    unfold OpsConsistent at h
    cases hfn : F[name.name]? with
    | none => exact .op_notin hfn
    | some fn =>
      simp only [hfn] at h
      cases hts : LFunc.opTypeSubst fn (.op m name ty) with
      | none => simp only [hts] at h
      | some tySubst =>
        simp only [hts] at h
        cases ty with
        | none => exact absurd h id
        | some ty_op => exact .op_in hfn h
  | app m fn arg ihfn iharg =>
    intro h; exact .app (ihfn h.1) (iharg h.2)
  | abs m name ty body ih =>
    intro h; exact .abs (ih h)
  | ite m c t f ihc iht ihf =>
    intro h; exact .ite (ihc h.1) (iht h.2.1) (ihf h.2.2)
  | eq m e1 e2 ih1 ih2 =>
    intro h; exact .eq (ih1 h.1) (ih2 h.2)
  | quant m k name ty tr body ihtr ihbody =>
    intro h; exact .quant (ihtr h.1) (ihbody h.2)

omit [DecidableEq T.IDMeta] in
/-- The executable check `LExpr.opsConsistent` is sound for `OpsConsistentR`: when it holds,
every operator of the factory in `e` is annotated with an instance of its generic type. -/
theorem opsConsistent_sound {F : @Factory T} {e : LExpr T.mono} :
    e.opsConsistent F = true → OpsConsistentR F e := by
  induction e with
  | op m name ty =>
    unfold LExpr.opsConsistent
    cases hfn : F[name.name]? with
    | none => exact fun _ => .op_notin hfn
    | some fn =>
      cases ty with
      | none => simp
      | some tyOp =>
        intro h
        obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp h
        exact .op_in hfn (LMonoTy.matchSubst_sound hS).symm
  | app m fn arg ihfn iharg =>
    simp only [LExpr.opsConsistent, Bool.and_eq_true]
    exact fun h => .app (ihfn h.1) (iharg h.2)
  | abs m name ty body ih => exact fun h => .abs (ih h)
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.opsConsistent, Bool.and_eq_true]
    exact fun h => .ite (ihc h.1.1) (iht h.1.2) (ihf h.2)
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.opsConsistent, Bool.and_eq_true]
    exact fun h => .eq (ih1 h.1) (ih2 h.2)
  | quant m k name ty tr body ihtr ihbody =>
    simp only [LExpr.opsConsistent, Bool.and_eq_true]
    exact fun h => .quant (ihtr h.1) (ihbody h.2)
  | const => exact fun _ => .const
  | bvar => exact fun _ => .bvar
  | fvar => exact fun _ => .fvar

/-! ### Factory assumptions -/

/-- A factory is well-typed when every function body type-checks at the
function's declared output type. -/
public def Factory.WellTyped [DecidableEq T.IDMeta] (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ body, (F[f]).body = some body →
    LExpr.HasTypeA [] body (F[f]).output ∧
    fvars_annotated_by (F[f]).inputs body

omit [DecidableEq T.IDMeta] in
/-- `Factory.WellTyped F` holds when every function body type-checks at the function's declared
    output type, with its free variables annotated at the function's formals. -/
public theorem Factory.WellTyped.intro [DecidableEq T.IDMeta] {F : @Factory T}
    (h :
      ∀ (f : String), (hf : f ∈ F) → ∀ body, (F[f]).body = some body →
        LExpr.HasTypeA [] body (F[f]).output ∧
        fvars_annotated_by (F[f]).inputs body) :
    Factory.WellTyped F := h

/-- A factory's concrete evaluators preserve well-typedness: if `ceval` returns
a result at the function's instantiated type (`LFunc.instTy`) and the arguments are
well-typed at the instantiated input types, then the result is well-typed at the
instantiated output type. -/
public def Factory.EvalWellTyped [DecidableEq T.IDMeta] (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ ceval, (F[f]).concreteEval = some ceval →
    ∀ (md : T.Metadata) (args : List (LExpr T.mono)) (result : LExpr T.mono) (tySubst : Subst),
      ceval md (some ((F[f]).instTy tySubst)) args = some result →
      List.Rel₂ (LExpr.HasTypeA []) args ((F[f]).inputs.map Prod.snd |>.map (LMonoTy.subst tySubst)) →
      LExpr.HasTypeA [] result (LMonoTy.subst tySubst (F[f]).output)

omit [DecidableEq T.IDMeta] in
/-- `Factory.EvalWellTyped F` holds when every concrete evaluator, called at an instance of its
    function's type on arguments well-typed at the instantiated inputs, returns a result
    well-typed at the instantiated output. -/
public theorem Factory.EvalWellTyped.intro [DecidableEq T.IDMeta] {F : @Factory T}
    (h :
      ∀ (f : String), (hf : f ∈ F) → ∀ ceval, (F[f]).concreteEval = some ceval →
        ∀ (md : T.Metadata) (args : List (LExpr T.mono)) (result : LExpr T.mono) (tySubst : Subst),
          ceval md (some ((F[f]).instTy tySubst)) args = some result →
          List.Rel₂ (LExpr.HasTypeA []) args
            ((F[f]).inputs.map Prod.snd |>.map (LMonoTy.subst tySubst)) →
          LExpr.HasTypeA [] result (LMonoTy.subst tySubst (F[f]).output)) :
    Factory.EvalWellTyped F := h

/-- `isConstr` faithfulness: `f.isConstr = true` implies `f` was generated
from a constructor in the TypeFactory. -/
public def Factory.ConstrWellFormed (F : @Factory T) (tf : @TypeFactory T.IDMeta) : Prop :=
  ∀ (f : LFunc T),
    f ∈ F.toArray →
    f.isConstr = true →
    ∃ (d : LDatatype T.IDMeta) (_ : d ∈ tf.allDatatypes)
      (c : LConstr T.IDMeta) (_ : c ∈ d.constrs),
      f = constrFunc c d

omit [DecidableEq T.IDMeta] in
/-- No constructor of a factory whose constructors come from the type factory `tf`
(`Factory.ConstrWellFormed`) produces a Boolean, when no datatype of `tf` is named `bool`:
each constructor's output is its datatype's type constructor applied to the datatype's
parameters, which no type substitution turns into `bool`. -/
theorem Factory.ConstrWellFormed.constrsNotBool {F : @Factory T} {tf : @TypeFactory T.IDMeta}
    (h : F.ConstrWellFormed tf) (hname : ∀ d ∈ tf.allDatatypes, d.name ≠ "bool") :
    F.ConstrsNotBool := by
  intro fn hfn hc S
  obtain ⟨d, hd, c, -, rfl⟩ := h fn hfn hc
  unfold LMonoTy.subst
  split <;> simp [constrFunc, dataDefault, data, LMonoTy.substCore, LMonoTy.bool, hname d hd]

omit [DecidableEq T.IDMeta] in
/-- `Factory.ConstrWellFormed F tf` holds when every constructor function of `F` is the
    function of a constructor of a datatype of `tf`. -/
public theorem Factory.ConstrWellFormed.intro {F : @Factory T} {tf : @TypeFactory T.IDMeta}
    (h :
      ∀ (f : LFunc T),
        f ∈ F.toArray →
        f.isConstr = true →
        ∃ (d : LDatatype T.IDMeta) (_ : d ∈ tf.allDatatypes)
          (c : LConstr T.IDMeta) (_ : c ∈ d.constrs),
          f = constrFunc c d) :
    Factory.ConstrWellFormed F tf := h

/-- Every function body in the factory satisfies `OpsConsistent` after type
instantiation via `applyTypeSubst`. -/
public def Factory.BodyOpsConsistent (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ body S, (F[f]).body = some body →
    OpsConsistent F (body.applyTypeSubst S)

omit [DecidableEq T.IDMeta] in
/-- `Factory.BodyOpsConsistent F` holds when every function body, at every type
    instantiation, annotates its operators as instances of their declared types in `F`. -/
public theorem Factory.BodyOpsConsistent.intro {F : @Factory T}
    (h :
      ∀ (f : String), (hf : f ∈ F) → ∀ body S, (F[f]).body = some body →
        OpsConsistent F (body.applyTypeSubst S)) :
    Factory.BodyOpsConsistent F := h

/-- Every concrete evaluator in the factory returns results that satisfy
`OpsConsistent`. -/
public def Factory.EvalOpsConsistent (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ ceval md opTy args result, (F[f]).concreteEval = some ceval →
    .some result = ceval md opTy args → OpsConsistent F result

omit [DecidableEq T.IDMeta] in
/-- `Factory.EvalOpsConsistent F` holds when every result of a concrete evaluator annotates its
    operators as instances of their declared types in `F`. -/
public theorem Factory.EvalOpsConsistent.intro {F : @Factory T}
    (h :
      ∀ (f : String), (hf : f ∈ F) → ∀ ceval md opTy args result,
        (F[f]).concreteEval = some ceval → .some result = ceval md opTy args →
        OpsConsistent F result) :
    Factory.EvalOpsConsistent F := h

/-- Every function body in the factory, after type instantiation, has fvar
annotations consistent with `tyMap`. -/
public def Factory.BodyAnnotated [DecidableEq T.IDMeta] (F : @Factory T)
    (tyMap : Map T.Identifier LMonoTy) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ body S, (F[f]).body = some body →
    fvars_annotated_by tyMap (body.applyTypeSubst S)

omit [DecidableEq T.IDMeta] in
/-- `Factory.BodyAnnotated F tyMap` holds when every function body, at every type
    instantiation, annotates each free variable `tyMap` types with that type. -/
public theorem Factory.BodyAnnotated.intro [DecidableEq T.IDMeta] {F : @Factory T}
    {tyMap : Map T.Identifier LMonoTy}
    (h :
      ∀ (f : String), (hf : f ∈ F) → ∀ body S, (F[f]).body = some body →
        fvars_annotated_by tyMap (body.applyTypeSubst S)) :
    Factory.BodyAnnotated F tyMap := h

/-- Every concrete evaluator in the factory returns results with fvar
annotations consistent with `tyMap`. -/
public def Factory.EvalAnnotated [DecidableEq T.IDMeta] (F : @Factory T)
    (tyMap : Map T.Identifier LMonoTy) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ ceval md opTy args result, (F[f]).concreteEval = some ceval →
    .some result = ceval md opTy args → fvars_annotated_by tyMap result

omit [DecidableEq T.IDMeta] in
/-- `Factory.EvalAnnotated F tyMap` holds when every result of a concrete evaluator annotates
    each free variable `tyMap` types with that type. -/
public theorem Factory.EvalAnnotated.intro [DecidableEq T.IDMeta] {F : @Factory T}
    {tyMap : Map T.Identifier LMonoTy}
    (h :
      ∀ (f : String), (hf : f ∈ F) → ∀ ceval md opTy args result,
        (F[f]).concreteEval = some ceval → .some result = ceval md opTy args →
        fvars_annotated_by tyMap result) :
    Factory.EvalAnnotated F tyMap := h

/-! ### Environment assumptions -/

/-- Environment values are well-typed: there is a type map `tyMap` such that
every env value is well-typed at its corresponding type, and every env key
has a type in the map. -/
structure Env.Typed [DecidableEq T.IDMeta] (env : Env T) where
  /-- The type map assigning types to environment keys. -/
  tyMap : Map T.Identifier LMonoTy
  /-- Every env value is well-typed at the type given by `tyMap`. -/
  wt : ∀ (x : T.Identifier) (e : LExpr T.mono) (ty : LMonoTy),
    env x = some e → Map.find? tyMap x = some ty → LExpr.HasTypeA [] e ty
  /-- Every env key has a type in `tyMap`. -/
  cover : ∀ (x : T.Identifier) (e : LExpr T.mono),
    env x = some e → ∃ ty, Map.find? tyMap x = some ty

/-! ### Bundled assumptions -/

/-- Bundled well-formedness assumptions on the environment for step preservation.
- `typed` : `Env.Typed env` — environment maps identifiers to well-typed expressions
- `lc` : environment values are locally closed (`lcAt 0`)
- `ops` : environment values satisfy `OpsConsistent F`
- `annot` : environment values satisfy `fvars_annotated_by typed.tyMap`
-/
structure Env.StepWF (F : @Factory T) (env : Env T) where
  typed : Env.Typed env
  lc : ∀ (x : T.Identifier) (e : LExpr T.mono), env x = some e → LExpr.lcAt 0 e = true
  ops : ∀ (x : T.Identifier) (e : LExpr T.mono), env x = some e → OpsConsistent F e
  annot : ∀ (x : T.Identifier) (e : LExpr T.mono), env x = some e →
      fvars_annotated_by typed.tyMap e

/-! ### Sub-environments

Every assumption the denotational lemmas make of an environment is pointwise, so it holds
of any environment holding a subset of the bindings, with the same type map. -/

omit [DecidableEq T.IDMeta] in
/-- A sub-environment is typed by the same type map. -/
def Env.Typed.restrict {env₁ env₂ : Env T} (h : Env.Typed env₂) (hsub : Env.Sub env₁ env₂) :
    Env.Typed env₁ where
  tyMap := h.tyMap
  wt := fun x e ty hx hty => h.wt x e ty (hsub x e hx) hty
  cover := fun x e hx => h.cover x e (hsub x e hx)

/-- The step well-formedness of an environment restricts to a sub-environment, with the
same type map. -/
def Env.StepWF.restrict {F : @Factory T} {env₁ env₂ : Env T} (h : Env.StepWF F env₂)
    (hsub : Env.Sub env₁ env₂) : Env.StepWF F env₁ where
  typed := h.typed.restrict hsub
  lc := fun x e hx => h.lc x e (hsub x e hx)
  ops := fun x e hx => h.ops x e (hsub x e hx)
  annot := fun x e hx => h.annot x e (hsub x e hx)

/-- Bundled well-formedness assumptions on the factory for step preservation.
- `wt` : `Factory.WellTyped F` — factory function bodies are well-typed
- `evalWt` : `Factory.EvalWellTyped F` — concrete evaluators return well-typed results
- `bodyOps` : `Factory.BodyOpsConsistent F` — factory bodies satisfy `OpsConsistent` after substitution
- `evalOps` : `Factory.EvalOpsConsistent F` — concrete evaluators return `OpsConsistent` results
- `bodyAnnot` : `Factory.BodyAnnotated F tyMap` — factory bodies satisfy `fvars_annotated_by` after substitution
- `evalAnnot` : `Factory.EvalAnnotated F tyMap` — concrete evaluators return annotated results
-/
public structure Factory.StepWF (F : @Factory T) (tyMap : Map T.Identifier LMonoTy) where
  wt : Factory.WellTyped F
  evalWt : Factory.EvalWellTyped F
  bodyOps : Factory.BodyOpsConsistent F
  evalOps : Factory.EvalOpsConsistent F
  bodyAnnot : Factory.BodyAnnotated F tyMap
  evalAnnot : Factory.EvalAnnotated F tyMap

/-- Bundled well-formedness assumptions on the factory and type factory.
- `factoryWF` : `FactoryWF F` — factory is well-formed
- `constrWF` : `Factory.ConstrWellFormed F tf` — constructors are well-formed w.r.t. type factory
- `tfWF` : `TypeFactoryWF tf` — type factory is well-formed
-/
public structure Factory.WF (F : @Factory T) (tf : @TypeFactory T.IDMeta) where
  factoryWF : FactoryWF F
  constrWF : Factory.ConstrWellFormed F tf
  tfWF : TypeFactoryWF tf

end Lambda
