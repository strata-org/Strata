/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
import all Strata.Languages.Laurel.LaurelAST

/-!
# Properties of the Laurel AST

Properties of the definitions in `Strata.Languages.Laurel.LaurelAST`.

Key results:

- `highEq_source_irrel` — `highEq` ignores the source metadata of both
  arguments.
- `matchTypeArg_monotone` — type-argument inference only EXTENDS the accumulator;
  a binding already present in `acc` is preserved in the result.
-/

namespace Strata.Laurel

public section

/-- `highEq` only inspects the wrapped type values, never the source metadata
    of either argument. -/
theorem highEq_source_irrel (a b : HighTypeMd) (sa sb : FileRange) :
    highEq ⟨a.val, sa⟩ ⟨b.val, sb⟩ = highEq a b := by
  rw [highEq.eq_def, highEq.eq_def]

end

/-! ## Type-argument inference

This is the invariant the `.Applied` args-fold in `matchTypeArg` relies on: the fold
threads one accumulator through the recursive match of each positional argument, so a
type variable bound while matching an earlier argument must still be bound (unchanged)
when a later argument is matched — otherwise a consistency check against the earlier
binding (the `.TVar`/`some prev` arm) could not fire, and `Pair<T,T>` vs `Pair<int,bool>`
would spuriously succeed instead of failing. Monotonicity over the WHOLE function (every
constructor arm, not just the `.TVar` arm) is what makes that threading sound.
-/

/-- A left fold of `acc?.bind (matchTypeArg-like step)` over a list preserves any key the
    starting accumulator binds, given that each step preserves it. The `none` short-circuit
    (once the accumulator is `none` it stays `none`) forces every step before a `some` result
    to have itself produced `some`, so the per-step hypothesis applies at each stage. This is
    the fold half of `matchTypeArg_monotone`'s `.Applied` case. -/
private theorem foldl_bind_preserves {α : Type}
    (f : α → Std.HashMap String HighType → Option (Std.HashMap String HighType))
    (k : String) (v : HighType)
    (hstep : ∀ (x : α) (acc res : Std.HashMap String HighType),
        acc[k]? = some v → f x acc = some res → res[k]? = some v) :
    ∀ (L : List α) (start m : Std.HashMap String HighType),
    start[k]? = some v →
    L.foldl (fun acc? x => acc?.bind (fun mm => f x mm)) (some start) = some m →
    m[k]? = some v := by
  intro L
  induction L with
  | nil => intro start m hstart hfold; simp only [List.foldl_nil] at hfold; grind
  | cons x xs ih =>
    intro start m hstart hfold
    simp only [List.foldl_cons, Option.bind_some] at hfold
    cases hfx : f x start with
    | none =>
      -- once the accumulator is `none` the fold stays `none`, contradicting `… = some m`.
      have hnone : ∀ l : List α, l.foldl (fun acc? x => acc?.bind (fun mm => f x mm)) none = none := by
        intro l; induction l with
        | nil => rfl
        | cons y ys ih2 => simp only [List.foldl_cons, Option.bind_none]; exact ih2
      rw [hfx, hnone] at hfold; simp at hfold
    | some start' =>
      rw [hfx] at hfold
      exact ih start' m (hstep x start start' hstart hfx) hfold

/-- `matchTypeArg` is accumulator-monotone: any binding present in the input accumulator
    survives, unchanged, into a successful result. See the module docstring for why the
    `.Applied` args-fold depends on this. -/
public theorem matchTypeArg_monotone (declared actual : HighType)
    (acc m : Std.HashMap String HighType) (k : String) (v : HighType)
    (hk : acc[k]? = some v)
    (hm : matchTypeArg declared actual acc = some m) : m[k]? = some v := by
  induction declared, actual, acc using matchTypeArg.induct generalizing m with
  -- The `.Applied` args-fold: the head match preserves `k` (`ih1`), and each positional
  -- arg preserves it (`ihargs`, per-element via the `.attach` membership proof), so the
  -- fold threading `acc1` does too (`foldl_bind_preserves`).
  | case7 acc db dargs ab aargs hlen hname acc1 hrec ih1 ihargs =>
    simp only [matchTypeArg, hlen, hname, hrec, if_false, Bool.false_eq_true] at hm
    refine foldl_bind_preserves
      (fun (x : {p // p ∈ dargs.zip aargs}) mm => matchTypeArg x.1.fst.val x.1.snd.val mm)
      k v ?_ (dargs.zip aargs).attach acc1 m (ih1 acc1 hk hrec) hm
    intro x acc' res hacc' hf
    exact ihargs x.1.fst x.1.snd x.2 acc' res hacc' hf
  -- `.TMap`: a two-step bind (key then value); each step preserves `k` by its own IH.
  | case11 acc dk dv ak av ih1 ih2 =>
    simp only [matchTypeArg] at hm
    cases hd : matchTypeArg dk.val ak.val acc with
    | none => rw [hd] at hm; simp at hm
    | some acc' =>
      rw [hd] at hm; simp only [Option.bind_some] at hm
      exact ih2 acc' m (ih1 acc' hk hd) hm
  -- Every other arm either returns `acc` unchanged (`.TVar` consistent/insert, catch-all),
  -- fails outright (arity/name/shape mismatch → `none`, contradicting `= some m`), or recurses
  -- once into a child whose IH preserves `k` (`.TSet`). All uniform: unfold, then `grind`.
  | _ => simp only [matchTypeArg] at hm <;> grind

end Strata.Laurel
