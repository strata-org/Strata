/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashMap.Basic

/-! # Safe pointer-address caches

This module implements the "pointer address hashing" cache of Section 5 of
[Sealing Pointer-Based Optimizations Behind Pure Functions](https://arxiv.org/abs/2003.01685)
(Selsam, Hudon, de Moura).
Given a function `f: A -> B`, it builds a cache whose key is the pointer
address of `x:A` and the returned value `f (x:A)` is memoized (not calculated twice).
This pointer-address cache is safe to use for two reasons:

(1) The address of a Lean object doesn't change during its lifetime
  (uses reference counting). Other languages like Java or OCaml which uses the
  moving garbage collection don't have this property.
(2) The cache keeps a reference to the key objects, hence it is never
  deallocated by the garbage collector.

## How is it implemented?

Lean4 provides `ptrAddrUnsafe` and `ptrEq` which expose the address
of a Lean object, but using these is unsafe because they can distinguish between two
definitionally equivalent Lean terms.
To prevent the accident, Lean4 provides a safer alternative which is the
`withPtrAddr (x:A) (f:USize -> B) (h : ∀ (u₁ u₂ : USize), f u₁ = f u₂)` function.
The additional argument `h` must be given to `withPtrAddr` to ensure that
`f` returns identically regardless of the pointer address.

The paper & this file implement a cache lookup + update function using
the safe `withPtrAddr` function, with `A` being the key type and `B` being
the `(value type × cache type)`
(precisely speaking `B` is `cache type → (value type × cache type)`, but let's
 simplify it to just a pair type).

A challenge is to make `B` indistinguishable by comparison, which is needed
by the `h` argument of `withPtrAddr`. Constructing this isn't straightforward
for two reasons:
(1) The value type might not be a subsingleton (e.g., `String`).
   ("subsingleton" is just a fancy way of calling a set with indistinguishable
    elements, e.g., `Unit` or `False`)
(2) The cache type might not be a subsingleton (e.g., `HashMap` from `USize` to values)

To address (1), it defines a dependent wrapper type `Result f key` where `f`
is the function to memoize and `key` is the key to look up. For example, if
a key is `3`, the result is wrapped in the `Result f 3` type with a proof
that `f 3 = <the value>`. This `Result f 3` is a subsingleton because `f 3`
cannot have two different values.

To address (2), it uses a quotient type, specifically `Squash T` which makes
all elements of the set `T` as equal.
However, for consistency, the element of `Squash T` cannot be applied to any
function that can possibly distinguish differences, which will include many
useful functions of `T`.
In the case of `PtrCache`, `T` is `HashMap USize ...`. The cache itself is
`Squash`ed, so its contents are never observable as data; we only ever rewrite
it into another squashed cache (on insert) or read out a `Result f x` that is
uniquely determined by the query (on lookup).
-/

namespace Strata.PtrCache

public section

/-! ## §5.1 primitive: imprecise pointer-equality test

Lean core ships `withPtrEq`/`withPtrEqDecEq` (§3) and `withPtrAddr` (§5.2), but
not the imprecise variant of §5.1, so we add it here. -/

/-- The result of an imprecise pointer-equality test on `x` and `y`: either we
    learn nothing (`unknown`), or we obtain a proof that `x = y` (`yesEqual`). -/
inductive PtrEqResult {α : Type} (x y : α) : Type where
  | unknown  : PtrEqResult x y
  | yesEqual : x = y → PtrEqResult x y

/-- withPtrEqResultUnsafe and withPtrEqResult are not supported by Lean4's
    standard library. However, the behavior of withPtrEqResult and
    withPtrEqResultUnsafe is not distinguishable because the return
    types are both subsingleton. The two functions are precisely copies
    of the code in §5.1. -/
@[inline] unsafe def withPtrEqResultUnsafe {α β : Type} [Subsingleton β]
    (x y : α) (k : PtrEqResult x y → β) : β :=
  if ptrEq x y then k (.yesEqual lcProof) else k .unknown

/-- Imprecise pointer-equality test (§5.1). The reference implementation always
    reports `unknown`; the accelerated implementation reports `yesEqual` when
    `x` and `y` are pointer-identical. Sound because `β` is a subsingleton, so
    `k` returns the same value (up to equality) regardless of the branch. -/
@[implemented_by withPtrEqResultUnsafe]
def withPtrEqResult {α β : Type} [Subsingleton β]
    (x y : α) (k : PtrEqResult x y → β) : β :=
  k .unknown

/-! ## §5.1 proof-carrying value and cache entries -/

/-- A value together with a proof that it equals `f x`. For a fixed `x` this is
    a subsingleton (its only inhabitant is `f x`), so it can be returned from a
    `withPtrAddr`/`withPtrEqResult` continuation; but its value varies with `x`. -/
structure Result {α β : Type} (f : α → β) (x : α) where
  output : β
  h      : output = f x

instance {α β : Type} {f : α → β} {x : α} : Subsingleton (Result f x) :=
  ⟨fun a b => by
    cases a with | mk ao ah =>
    cases b with | mk bo bh =>
    subst ah; subst bh; rfl⟩

/-- A cache entry: an input node paired with its (proof-carrying) result. -/
structure Entry {α β : Type} (f : α → β) where
  input  : α
  result : Result f input

/-- A pointer-address cache for `f`. Backed by a `Std.HashMap` keyed by memory
    address (obtained transiently via `withPtrAddr`, never stored as data), and
    `Squash`ed so its contents are never observable — only the per-query
    `Result f x` (uniquely determined by `x`) is ever read out. -/
def PtrCache {α β : Type} (f : α → β) : Type :=
  Squash (Std.HashMap USize (List (Entry f)))

/-- The empty pointer cache. -/
def PtrCache.empty {α β : Type} {f : α → β} : PtrCache f := Squash.mk {}

instance {α β : Type} {f : α → β} : Subsingleton (PtrCache f) :=
  inferInstanceAs (Subsingleton (Squash _))

/-- The state monad threading a `PtrCache f`, producing a `Result f x`. -/
abbrev PtrCacheM {α β : Type} (f : α → β) (x : α) : Type :=
  StateM (PtrCache f) (Result f x)

/-! ## §5.1: search within a bucket by imprecise pointer equality -/

/-- Search a bucket for `x₀` using only pointer equality (never structural
    equality). On a hit, return the stored result re-typed at `x₀`. On a miss,
    run the continuation `k`, record the freshly computed entry via `update`,
    and return it. -/
def evalImpreciseBucket {α β : Type} {f : α → β} {γ : Type} [Subsingleton γ]
    (x₀ : α) (k : StateM γ (Result f x₀)) (update : Entry f → StateM γ Unit)
    (es : List (Entry f)) : StateM γ (Result f x₀) :=
  match es with
  | [] => do
    let r ← k
    update ⟨x₀, r⟩
    pure r
  | ⟨x, r⟩ :: rest =>
    withPtrEqResult x x₀ fun pr =>
      match pr with
      | .yesEqual h => pure (h ▸ r)
      | .unknown    => evalImpreciseBucket x₀ k update rest
  termination_by es

/-! ## §5.2: the pointer-address cache lookup -/

/-- Query the pointer cache for `x`, memoizing `f x` by memory address. On a
    miss, `k` (typically the caller recursing on `x`'s children) computes the
    result, which is then inserted into the bucket for `x`'s address. -/
def evalPtrCache {α β : Type} {f : α → β} (x : α) (k : PtrCacheM f x) :
    PtrCacheM f x := do
  let s ← get
  withPtrAddr x
    (fun u => Squash.lift s fun m =>
      let update : Entry f → StateM (PtrCache f) Unit := fun e =>
        modify fun c => Squash.lift c fun m' =>
          Squash.mk (m'.insert u (e :: m'.getD u []))
      evalImpreciseBucket x k update (m.getD u []))
    (fun _ _ => Subsingleton.elim _ _)

/-- **The pointer cache is a transparent optimization.** Running any
    `PtrCacheM f x` computation from any starting cache yields a value equal to
    `f x`, on the nose. The cache's (unobservable, squashed) contents cannot
    affect the result — this is guaranteed for free by the `Result.h` proof that
    every entry carries, so no separate correctness test is ever needed for a
    cache built on this interface. -/
theorem run'_output_eq {α β : Type} {f : α → β} {x : α}
    (m : PtrCacheM f x) (c : PtrCache f) : (m.run' c).output = f x :=
  (m.run' c).h

end

end Strata.PtrCache
