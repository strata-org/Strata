/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.TypeFactory

/-! ## Declarative Well-Formedness of Datatypes

Inductive relations specifying when a mutual datatype block's constructor
argument types are well-formed, each the declarative counterpart of a checker
function in `TypeFactory.lean`:

* `TyNameAppears`  ↔ `tyNameAppearsIn`
* `UniformOccur`   ↔ `checkUniform`
* `NotNested`      ↔ `checkNotNested`
* `StrictPosUnif`  ↔ `checkStrictPosUnifTy`
* `TyInhab` / `TySymInhab` / `ConstrInhab` ↔ `ty_inhab` / `typesym_inhab`

These are `Lambda`-level (about `LMonoTy` / `MutualDatatype` / `TypeFactory`) and
carry no Core-specific data. The Core-facing bundle `MutualADTWF` (which mentions
`LContext CoreLParams`) lives in `Strata.Languages.Core.DatatypeTypeSpec`.

Because `LMonoTy.arrow t1 t2` is definitionally `LMonoTy.tcons "arrow" [t1, t2]`,
the checkers that match `.arrow` *before* the general `.tcons` case
(`checkNotNested`, `checkStrictPosUnifTy`) behave differently on a binary arrow
than on an arbitrary type constructor. The inductive relations reproduce that
match order by guarding the general `.tcons` constructor with `¬ IsBinaryArrow`.
-/

namespace Lambda

public section

/-- `ty` is a binary arrow, i.e. it is `t1 → t2` for some `t1`, `t2`. Used to
    guard the general `.tcons` cases of `NotNested` / `StrictPosUnif` so they do
    not overlap the dedicated arrow case (mirroring the checkers' match order). -/
def IsBinaryArrow (ty : LMonoTy) : Prop := ∃ t1 t2, ty = .arrow t1 t2

/-- The type name `n` occurs somewhere in `ty`. Declarative counterpart of
    `Lambda.tyNameAppearsIn` (its `= true` cases). Its negation is the
    "`n` is absent from `ty`" condition used by `NotNested` / `StrictPosUnif`. -/
inductive TyNameAppears (n : String) : LMonoTy → Prop where
  /-- `n` is the head constructor. -/
  | head : ∀ args, TyNameAppears n (.tcons n args)
  /-- `n` occurs in one of the arguments (under any head). -/
  | arg  : ∀ n1 args t, t ∈ args → TyNameAppears n t → TyNameAppears n (.tcons n1 args)

/-- The type name `n` does not occur in `ty`. -/
def TyNameAbsent (n : String) (ty : LMonoTy) : Prop := ¬ TyNameAppears n ty

/--
Every occurrence of the type name `n` in `ty` is applied to exactly `args`.
Declarative counterpart of `Lambda.checkUniform _ n args ty` returning `.ok`.

Note (mirroring the checker): once a uniform occurrence `n args` is found, its
arguments are *not* re-scanned — a nested occurrence like `n (n ...)` is caught
by the `n ≠ head` branch requiring uniformity of the inner arguments, which
fails when the inner head is `n` applied to different arguments.
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
arguments in `ty`. Declarative counterpart of
`Lambda.checkNotNested _ block ty` returning `.ok`.

A block datatype appearing at the head of a `.tcons` is fine (that is a direct,
possibly recursive, reference); what is rejected is a block datatype buried in
the arguments of a non-block head.
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
`ty` is strictly positive and uniform for `block`. Declarative counterpart of
`Lambda.checkStrictPosUnifTy _ block ty` returning `.ok`.

* No datatype of `block` may appear to the left of an arrow (strict positivity).
* At a non-arrow position, every block datatype must occur uniformly (applied to
  its own `typeArgs`).

WARNING: this is the *checker's* restriction, which is strictly STRONGER than
the textbook notion of strict positivity, so do not assume the standard
definition when proving against it. Textbook strict positivity of `T` in an
argument type `A` allows: `T` absent from `A`; `A = T u₁…uₙ` with `T` absent from
the `uᵢ`; `A = B → C` with `T` absent from `B` and strictly positive in `C`; and
*nested* positivity `A = D … b` where `T` is strictly positive in the `bᵢ`. The
Strata check differs on the last two:

* Uniformity (the `base` case) requires each recursive occurrence to be applied
  to *exactly* the datatype's own `typeArgs`, so non-uniform/non-regular
  recursion such as `Powl a = Cons (Powl (a, a))` is rejected even though it is
  textbook strictly positive.
* Nested positivity is forbidden entirely — by `NotNested` (the other half of
  `ConstrArgWF`), not here — so `Rose = Node (List Rose)` is rejected.

The relation is therefore SOUND but INCOMPLETE w.r.t. textbook strict positivity:
everything it accepts is strictly positive, but it rejects legitimate nested and
non-uniform datatypes. This is a deliberate language restriction (it keeps
eliminator generation and the conservative inhabitance check tractable).
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
    (`StrictPosUnif`). Declarative counterpart of the per-argument body of
    `Lambda.checkConstructorArgsWF`. Together these are strictly stronger than
    textbook strict positivity — see the `StrictPosUnif` docstring. -/
def ConstrArgWF (block : MutualDatatype Unit) (ty : LMonoTy) : Prop :=
  NotNested block ty ∧ StrictPosUnif block ty

/-! ### Inhabitance

Inhabitance relative to the datatype factory `adts`, as three mutually inductive
relations mirroring the checker in `TypeFactory.lean`:

* `TyInhab`     ↔ `Lambda.ty_inhab`       — a monotype is inhabited.
* `TySymInhab`  ↔ `Lambda.typesym_inhab`  — a type symbol (constructor name) is
  inhabited (`adt_inhab a := typesym_inhab adts [] a`).
* `ConstrInhab` — a constructor is inhabited, i.e. all its argument types are.

Being least-fixpoint predicates, these capture exactly the checker's memoized
computation: a datatype reachable only through a cycle back to itself is *not*
inhabited (the checker marks such `seen` symbols `false`, and there is no
inductive derivation for it here).

The check is deliberately conservative: `TyInhab (.tcons name args)` requires
both that the head symbol is inhabited *and* that every actual argument is
inhabited (so e.g. `List Empty` is rejected even though it is truly inhabited by
`Nil`) — matching `ty_inhab`.
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

/-- A type symbol is inhabited. Counterpart of `Lambda.typesym_inhab`. -/
inductive TySymInhab (adts : @TypeFactory Unit) : String → Prop where
  /-- A non-datatype symbol (external / known type) is assumed inhabited. -/
  | external : ∀ name, adts.getType name = none → TySymInhab adts name
  /-- A datatype symbol is inhabited when it has an inhabited constructor `c`
      (the witness is taken explicitly rather than existentially, to keep the
      mutual inductive non-nested). -/
  | datatype : ∀ name d c, adts.getType name = some d →
      c ∈ d.constrs → ConstrInhab adts c → TySymInhab adts name

/-- A constructor is inhabited when all of its (generic) argument types are.
    Counterpart of the inner `foldlM` in `Lambda.typesym_inhab`. -/
inductive ConstrInhab (adts : @TypeFactory Unit) : LConstr Unit → Prop where
  | mk : ∀ c, (∀ arg ∈ c.args, TyInhab adts arg.2) → ConstrInhab adts c
end

end -- public section

end Lambda
