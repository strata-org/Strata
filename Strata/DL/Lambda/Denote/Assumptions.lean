/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Semantics
import all Strata.DL.Lambda.TypeFactoryWF
import all Strata.DL.Lambda.FactoryWF

/-!
## Typing Assumptions

Collects all well-formedness and typing assumptions used by the denotational
semantics proofs. Semantic (denotation-level) assumptions live in
`LExprSemanticsConsistent`.

### Expression-level predicates (TODO: prove satisfied after `LExpr.resolve`)
- `fvars_annotated_by` — free variable annotations match a type map
- `OpsConsistent` — operator type annotations are valid factory instantiations

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
-/

namespace Lambda

variable {T : LExprParams} [DecidableEq T.IDMeta]

/-! ### Expression-level predicates -/

/-- Every fvar in `e` whose name is in `tyMap` is annotated with the
corresponding type. -/
def fvars_annotated_by [DecidableEq T.IDMeta]
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

/-- Every `.op` node in `e` whose name is in the factory has a type annotation
that is a valid instantiation of the function's generic type (via `opTypeSubst`).
This is checked at every `.op` node directly, not just at complete calls. -/
def OpsConsistent (F : @Factory T) : LExpr T.mono → Prop := fun e =>
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

/-! ### Factory assumptions -/

/-- A factory is well-typed when every function body type-checks at the
function's declared output type. -/
def Factory.WellTyped [DecidableEq T.IDMeta] (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ body, (F[f]).body = some body →
    LExpr.HasTypeA [] body (F[f]).output ∧
    fvars_annotated_by (F[f]).inputs body

/-- A factory's concrete evaluators preserve well-typedness: if `ceval` returns
a result and the arguments are well-typed at the instantiated input types,
then the result is well-typed at the instantiated output type. -/
def Factory.EvalWellTyped [DecidableEq T.IDMeta] (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ ceval, (F[f]).concreteEval = some ceval →
    ∀ (md : T.Metadata) (args : List (LExpr T.mono)) (result : LExpr T.mono) (tySubst : Subst),
      ceval md args = some result →
      List.Forall₂ (LExpr.HasTypeA []) args ((F[f]).inputs.map Prod.snd |>.map (LMonoTy.subst tySubst)) →
      LExpr.HasTypeA [] result (LMonoTy.subst tySubst (F[f]).output)

/-- `isConstr` faithfulness: `f.isConstr = true` implies `f` was generated
from a constructor in the TypeFactory. -/
def Factory.ConstrWellFormed (F : @Factory T) (tf : @TypeFactory T.IDMeta) : Prop :=
  ∀ (f : LFunc T),
    f ∈ F.toArray →
    f.isConstr = true →
    ∃ (d : LDatatype T.IDMeta) (_ : d ∈ tf.allDatatypes)
      (c : LConstr T.IDMeta) (_ : c ∈ d.constrs),
      f = constrFunc c d

/-- Every function body in the factory satisfies `OpsConsistent` after type
instantiation via `applySubst`. -/
def Factory.BodyOpsConsistent (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ body S, (F[f]).body = some body →
    OpsConsistent F (body.applySubst S)

/-- Every concrete evaluator in the factory returns results that satisfy
`OpsConsistent`. -/
def Factory.EvalOpsConsistent (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ ceval md args result, (F[f]).concreteEval = some ceval →
    .some result = ceval md args → OpsConsistent F result

/-- Every function body in the factory, after type instantiation, has fvar
annotations consistent with `tyMap`. -/
def Factory.BodyAnnotated [DecidableEq T.IDMeta] (F : @Factory T)
    (tyMap : Map T.Identifier LMonoTy) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ body S, (F[f]).body = some body →
    fvars_annotated_by tyMap (body.applySubst S)

/-- Every concrete evaluator in the factory returns results with fvar
annotations consistent with `tyMap`. -/
def Factory.EvalAnnotated [DecidableEq T.IDMeta] (F : @Factory T)
    (tyMap : Map T.Identifier LMonoTy) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ ceval md args result, (F[f]).concreteEval = some ceval →
    .some result = ceval md args → fvars_annotated_by tyMap result

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

/-- Bundled well-formedness assumptions on the factory for step preservation.
- `wt` : `Factory.WellTyped F` — factory function bodies are well-typed
- `evalWt` : `Factory.EvalWellTyped F` — concrete evaluators return well-typed results
- `bodyOps` : `Factory.BodyOpsConsistent F` — factory bodies satisfy `OpsConsistent` after substitution
- `evalOps` : `Factory.EvalOpsConsistent F` — concrete evaluators return `OpsConsistent` results
- `bodyAnnot` : `Factory.BodyAnnotated F tyMap` — factory bodies satisfy `fvars_annotated_by` after substitution
- `evalAnnot` : `Factory.EvalAnnotated F tyMap` — concrete evaluators return annotated results
-/
structure Factory.StepWF (F : @Factory T) (tyMap : Map T.Identifier LMonoTy) where
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
structure Factory.WF (F : @Factory T) (tf : @TypeFactory T.IDMeta) where
  factoryWF : FactoryWF F
  constrWF : Factory.ConstrWellFormed F tf
  tfWF : TypeFactoryWF tf

end Lambda
