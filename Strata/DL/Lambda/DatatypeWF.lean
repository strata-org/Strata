/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.TypeFactory

/-! ## Declarative Well-Formedness of Datatypes

Inductive relations specifying when a mutual datatype block's constructor
argument types are well-formed: `TyNameAppears`, `UniformOccur`, `NotNested`,
`StrictPosUnif`, and the inhabitance relations `TyInhab` / `TySymInhab` /
`ConstrInhab`.

These are `Lambda`-level (`LMonoTy` / `MutualDatatype` / `TypeFactory`); the
Core-facing bundle `MutualADTWF` lives in `Strata.Languages.Core.DatatypeTypeSpec`.

Since `LMonoTy.arrow t1 t2` is definitionally `LMonoTy.tcons "arrow" [t1, t2]`, the
general `.tcons` cases below are guarded with `¬ IsBinaryArrow` so an arrow is
handled only by its dedicated case.
-/

namespace Lambda

public section

/-- `ty` is a binary arrow, i.e. it is `t1 → t2` for some `t1`, `t2`. Guards the
    general `.tcons` cases of `NotNested` / `StrictPosUnif` so they do not overlap
    the dedicated arrow case. -/
def IsBinaryArrow (ty : LMonoTy) : Prop := ∃ t1 t2, ty = .arrow t1 t2

/-- The type name `n` occurs somewhere in `ty`. Its negation is the
    "`n` is absent from `ty`" condition used by `NotNested` / `StrictPosUnif`. -/
inductive TyNameAppears (n : String) : LMonoTy → Prop where
  /-- `n` is the head constructor. -/
  | head : ∀ args, TyNameAppears n (.tcons n args)
  /-- `n` occurs in one of the arguments (under any head). -/
  | arg  : ∀ n1 args t, t ∈ args → TyNameAppears n t → TyNameAppears n (.tcons n1 args)

/-- The type name `n` does not occur in `ty`. -/
def TyNameAbsent (n : String) (ty : LMonoTy) : Prop := ¬ TyNameAppears n ty

/--
Every occurrence of type constructor `n` in the type `ty` is applied to exactly
`args`. This is the primitive `StrictPosUnif` uses to enforce uniform (regular)
recursion; it calls it with `args` = the datatype's own `typeArgs`. "Uniform"
means recursive uses stay on the same parameters — not Rocq's "uniform parameter".

With `n = List`, `args = [a]` (i.e. checking types for uniform use of `List a`):
* uniform:     `a`, `List a`, `Pair (List a) bool`
* not uniform: `List bool`, `List (List a)`   (`List` applied to non-`a`)
-/
inductive UniformOccur (n : String) (args : LMonoTys) : LMonoTy → Prop where
  /-- A type variable contains no occurrence of `n`. -/
  | ftvar  : ∀ v, UniformOccur n args (.ftvar v)
  /-- A bitvector contains no occurrence of `n`. -/
  | bitvec : ∀ sz, UniformOccur n args (.bitvec sz)
  /-- `n` applied to exactly `args`: a uniform occurrence. -/
  | self   : UniformOccur n args (.tcons n args)
  /-- A different head `n1 ≠ n`: every argument must be uniform in `n`. -/
  | other  : ∀ n1 args1, n1 ≠ n → (∀ t ∈ args1, UniformOccur n args t) →
      UniformOccur n args (.tcons n1 args1)

/--
No datatype of `block` occurs *nested* inside another type constructor's
arguments in `ty`.

A block datatype at the head of a `.tcons` is a direct (possibly recursive)
reference and is fine; one buried in a non-block head's arguments is rejected.

With `Tree` in the block: `Tree a`, `bool → Tree a` ok; `List (Tree a)` rejected.
-/
inductive NotNested (block : MutualDatatype Unit) : LMonoTy → Prop where
  /-- Type variables are never nested. -/
  | ftvar  : ∀ v, NotNested block (.ftvar v)
  /-- Bitvectors are never nested. -/
  | bitvec : ∀ sz, NotNested block (.bitvec sz)
  /-- An arrow: recurse into both sides (matched before the general `.tcons`). -/
  | arrow  : ∀ t1 t2, NotNested block t1 → NotNested block t2 →
      NotNested block (.arrow t1 t2)
  /-- A block datatype at the head is allowed with no further obligation. -/
  | headBlock : ∀ n args, n ∈ block.map (·.name) →
      NotNested block (.tcons n args)
  /-- A non-block, non-arrow head: no block datatype may appear anywhere in its
      arguments, and each argument is itself not-nested. -/
  | headOther : ∀ n args, ¬ IsBinaryArrow (.tcons n args) → n ∉ block.map (·.name) →
      (∀ d ∈ block, ∀ a ∈ args, TyNameAbsent d.name a) →
      (∀ a ∈ args, NotNested block a) →
      NotNested block (.tcons n args)

/--
`ty` is strictly positive and uniform for `block`:
* no `block` datatype occurs left of an arrow (strict positivity, the `arrow` case);
* at non-arrow positions, every `block` datatype occurs uniformly — delegated to
  `UniformOccur` (the `base` case).

With `T` in the block declared `T a`:
* ok:                    `T a`, `bool → T a`, `Pair a (T a)`
* rejected (positivity): `(T a → bool) → T a`

Stronger than textbook strict positivity: uniformity bars non-regular recursion
(see `UniformOccur`), and nested positivity (`Rose = Node (List (Rose a))`) is
barred by `NotNested`. Sound but incomplete — a deliberate restriction.
Ref: https://rocq-prover.org/doc/V9.2.0/refman/language/core/inductive.html#well-formed-inductive-definitions
-/
inductive StrictPosUnif (block : MutualDatatype Unit) : LMonoTy → Prop where
  /-- An arrow: no block datatype in the domain; recurse into the codomain
      (matched before the general base case). -/
  | arrow : ∀ t1 t2, (∀ d ∈ block, TyNameAbsent d.name t1) →
      StrictPosUnif block t2 → StrictPosUnif block (.arrow t1 t2)
  /-- A non-arrow position: every block datatype occurs uniformly. -/
  | base  : ∀ ty, ¬ IsBinaryArrow ty →
      (∀ d ∈ block, UniformOccur d.name (d.typeArgs.map .ftvar) ty) →
      StrictPosUnif block ty

/-- A single constructor-argument type is well-formed for `block`: not nested
    (`NotNested`, which rules out nested positivity) and strictly-positive/uniform
    (`StrictPosUnif`). Together these are strictly stronger than textbook strict
    positivity — see the `StrictPosUnif` docstring. -/
def ConstrArgWF (block : MutualDatatype Unit) (ty : LMonoTy) : Prop :=
  NotNested block ty ∧ StrictPosUnif block ty

/-! ### Inhabitance

Inhabitance relative to the datatype factory `adts`, as three mutually inductive
relations:

* `TyInhab`     — a monotype is inhabited.
* `TySymInhab`  — a type symbol is inhabited.
* `ConstrInhab` — a constructor is inhabited (all its argument types are).

As least-fixpoint predicates, a datatype inhabited only through a cycle back to
itself has no derivation and is not inhabited. Inhabitance is conservative:
`TyInhab (.tcons name args)` requires both the head symbol and every argument
inhabited (so `List Empty` is rejected).
-/
mutual
inductive TyInhab (adts : @TypeFactory Unit) : LMonoTy → Prop where
  /-- Type variables are inhabited. -/
  | ftvar  : ∀ v, TyInhab adts (.ftvar v)
  /-- Bitvectors are inhabited. -/
  | bitvec : ∀ sz, TyInhab adts (.bitvec sz)
  /-- `name args` is inhabited when the symbol `name` is inhabited and every
      argument is inhabited. -/
  | tcons  : ∀ name args, TySymInhab adts name →
      (∀ a ∈ args, TyInhab adts a) → TyInhab adts (.tcons name args)

/-- A type symbol is inhabited. -/
inductive TySymInhab (adts : @TypeFactory Unit) : String → Prop where
  /-- A non-datatype symbol (external / known type) is assumed inhabited. -/
  | external : ∀ name, adts.getType name = none → TySymInhab adts name
  /-- A datatype symbol is inhabited when it has an inhabited constructor `c`
      (the witness is taken explicitly rather than existentially, to keep the
      mutual inductive non-nested). -/
  | datatype : ∀ name d c, adts.getType name = some d →
      c ∈ d.constrs → ConstrInhab adts c → TySymInhab adts name

/-- A constructor is inhabited when all of its (generic) argument types are. -/
inductive ConstrInhab (adts : @TypeFactory Unit) : LConstr Unit → Prop where
  | mk : ∀ c, (∀ arg ∈ c.args, TyInhab adts arg.2) → ConstrInhab adts c
end

end -- public section

end Lambda
