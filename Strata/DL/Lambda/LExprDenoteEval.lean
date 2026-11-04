/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LExprDenote
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.LExprWF

/-!
## Denotational Evaluation over Value Stores

An evaluator for Lambda expressions whose variables are bound in a store of
*semantic* values (elements of `SortDenote`), computed with `LExpr.denote`.
Its laws are in `Strata.DL.Lambda.LExprDenoteEvalProps`.

- `SemValue` — a runtime value: a sort and an element of its denotation under a
  type-constructor interpretation; `SemValue.ofBool`, `ofInt`, `ofBitVec`, `ofConst`
  build values
- `ModeledFactory` — a factory bundled with a consistent interpretation
- `ValStore` — a store of semantic values; `ValStore.Defines` says a store binds
  every free variable of an expression
- `LExpr.denoteEval` — evaluation: annotate every free variable with the sort of its
  stored value (`LExpr.annotateFvars`), type check at a ground type, and denote

Evaluation is restricted to monomorphic code.  Free variables are annotated with ground
sorts, so an expression whose operator or binder annotations mention a type variable does
not type check and has no value: a polymorphic procedure body is stuck.

A function's type parameters are read at every sort: its axioms must hold under every
type-variable valuation (`Factory.AxiomsSatisfied`).  Procedures with type parameters are not
yet given a meaning (their bodies are stuck); when they are, their parameters should be read
at every sort, as functions' are.  A residual type variable, which no declaration binds,
denotes the sort the model chooses for it (`ModeledFactory.tyVarVal`), as an opaque type
denotes the carrier the model chooses for it.  An assumption that holds at some sort
therefore holds in the model that chooses that sort, and a condition is valid only if it
holds under every choice.  This includes a top-level `axiom` whose expression mentions a
type variable: it is assumed at the model's chosen sort only, so a phase that instantiates
such an axiom at several sorts assumes more than its input and is not sound.
-/

namespace Lambda

public section

/-! ### Semantic values -/

/-- A runtime value: a sort together with an element of its denotation under the
type-constructor interpretation `tc` that produced it. -/
structure SemValue : Type 1 where
  /-- The interpretation of type constructors the value was produced under. -/
  tc : TyConstrInterp
  /-- The sort of the value. -/
  sort : LSort
  /-- The element of the sort's denotation under `tc`. -/
  val : SortDenote tc sort

/-- Read the value `v` as an element of sort `s` under `tc`, if it has that sort and
was produced under `tc`. -/
noncomputable def SemValue.read (v : SemValue) (tc : TyConstrInterp) (s : LSort) :
    Option (SortDenote tc s) :=
  open Classical in
  if h : v.tc = tc ∧ v.sort = s then
    some (cast (by obtain ⟨h1, h2⟩ := h; rw [h1, h2]) v.val)
  else none

/-- The Boolean value `b` under `tc`. -/
@[expose] def SemValue.ofBool (tc : TyConstrInterp) (b : Bool) : SemValue :=
  ⟨tc, .bool, b⟩

/-- The integer value `i` under `tc`. -/
@[expose] def SemValue.ofInt (tc : TyConstrInterp) (i : Int) : SemValue :=
  ⟨tc, .int, i⟩

/-- The width-`n` bitvector value `w` under `tc`. -/
@[expose] def SemValue.ofBitVec (tc : TyConstrInterp) (n : Nat) (w : BitVec n) : SemValue :=
  ⟨tc, .bitvec n, w⟩

/-! ### Modeled factories -/

/-- A factory bundled with a consistent interpretation of its functions, axioms,
and datatypes. -/
structure ModeledFactory (T : LExprParams) [DecidableEq T.IDMeta] : Type 1 where
  /-- The factory of functions. -/
  factory : @Factory T
  /-- A consistent interpretation of `factory`. -/
  model : Interp factory
  /-- The sort each residual type variable denotes. -/
  tyVarVal : TyVarVal

/-! ### Evaluation -/

variable {T : LExprParams}

/-- A value store: each variable is bound to a semantic value, or unbound. -/
abbrev ValStore (T : LExprParams) := Identifier T.IDMeta → Option SemValue

/-- The type annotation a value store gives a variable: the sort of its value. -/
@[expose] def ValStore.ann (σ : ValStore T) : Identifier T.IDMeta → Option LMonoTy :=
  fun x => (σ x).map (·.sort.toMonoTy)

/-- The free-variable valuation that reads every variable from the store, and
picks a default value for a variable that is unbound or bound at another sort or
interpretation. -/
noncomputable def ValStore.fvarVal (tc : TyConstrInterp) [TyConstrInterp.AllInhabited tc]
    (σ : ValStore T) : FreeVarVal T tc :=
  fun x s => ((σ x).bind (·.read tc s)).getD default

/-- A fixed type-variable valuation, used where the choice cannot matter: to state that
a type is ground, and to denote literals, whose types are ground. -/
@[expose] def refTyVarVal : TyVarVal := fun _ => .bool

/-- The value of the literal `c` under `tc`. -/
@[expose] def SemValue.ofConst (tc : TyConstrInterp) (c : LConst) : SemValue :=
  ⟨tc, c.ty.substTyVars refTyVarVal, denoteConst tc refTyVarVal c⟩

/-- The type `τ` is ground: it is the type of the sort it denotes, so it mentions no type
variable and denotes the same sort under every type-variable valuation
(`LMonoTy.IsGround.substTyVars_eq`). -/
abbrev LMonoTy.IsGround (τ : LMonoTy) : Prop := (τ.substTyVars refTyVarVal).toMonoTy = τ

/-- Every free variable of `e` is bound in `σ` to a value produced under `tc`. -/
@[expose] def ValStore.Defines [DecidableEq T.IDMeta] (σ : ValStore T)
    (tc : TyConstrInterp) (e : LExpr T.mono) : Prop :=
  ∀ x ∈ LExpr.LExpr.getVars e, ∃ v, σ x = some v ∧ v.tc = tc

/-- The compiled stand-in for `LExpr.denoteEval`, which is not computable (it decides
equalities and quantifiers over denotations).  Programs never run the evaluator; the
stand-in only lets languages that use it in their (data) definitions compile, as a
`PureExpr` carries its evaluator at run time.

It never returns.  A stand-in that returned a result (such as `none`) would disagree with
`denoteEval`, and `native_decide`, which trusts compiled code, could then prove `False`;
with this one, a `native_decide` goal that evaluates `denoteEval` does not terminate. -/
partial def LExpr.denoteEvalCode [DecidableEq T.IDMeta] (M : ModeledFactory T) (σ : ValStore T)
    (e : LExpr T.mono) : Option SemValue :=
  LExpr.denoteEvalCode M σ e

/-- The result of evaluating `e`, given a typing derivation of its annotation. -/
noncomputable def LExpr.denoteEvalResult [DecidableEq T.IDMeta] (M : ModeledFactory T)
    (σ : ValStore T) (e : LExpr T.mono) (τ : LMonoTy)
    (h : (e.annotateFvars σ.ann).HasTypeA [] τ) : SemValue :=
  letI := M.model.allInhabited
  ⟨M.model.tcInterp, τ.substTyVars M.tyVarVal,
    LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
      M.tyVarVal .nil (e.annotateFvars σ.ann) τ h⟩

/-- **Denotational evaluation.**  Annotate every free variable of `e` with the sort
of its stored value, type check, and denote under the factory's model, with the sorts it
chooses for type variables.  Evaluation
fails (`none`) when a free variable is unbound or bound to a value of another
model, or when the annotated expression is not well-typed at a ground type. -/
@[implemented_by LExpr.denoteEvalCode]
noncomputable def LExpr.denoteEval [DecidableEq T.IDMeta] (M : ModeledFactory T)
    (σ : ValStore T) (e : LExpr T.mono) : Option SemValue :=
  open Classical in
  if σ.Defines M.model.tcInterp e then
    match h : LExpr.typeCheck [] (e.annotateFvars σ.ann) with
    | some τ =>
      if τ.IsGround then some (e.denoteEvalResult M σ τ (LExpr.typeCheck_to_HasTypeA h))
      else none
    | none => none
  else none

end -- public section

end Lambda
