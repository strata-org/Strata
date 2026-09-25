/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
# Non-vacuity smoke test for the refactored-encoder soundness chain

Builds a CONCRETE, non-trivial `ProofObligation` (two nondet int vars, an equality assumption, a
`distinct` group, and an equality goal), PROVES it satisfies every well-formedness precondition
(`ProofObligation.WF` + `Factory.SimpWF` + the datatype-name side-condition), and then APPLIES the
headline `obligation_valid_of_unsatWithNegObl` to conclude that the emitted query's `UnsatWithNegObl` implies the
obligation's denotational validity.

This confirms the WF definitions are not vacuous: a real obligation over a real factory satisfies them,
and the end-to-end theorem fires on it. The factory carries one user function `g : int → int`
(`Factory.ofArray #[g]`); `Factory.SimpWF` is proven for it (the `nonPredefined F = [g]` structure is
recovered without `DecidableEq (LFunc)` via a length-1 argument + the public `Factory.ofArray_mem`). The
obligation exercises all four `PathEntryWF` constructors + `goalWF` + the `CoreCtx.NamesWF` machinery
inside `collect_WF` (whose freshness/nodup now genuinely spans a factory name `g` and the vars `x`, `y`).
-/

module

public import Strata.Languages.Core.VerifiedSMTGen.EncoderSound
import all Strata.Languages.Core.VerifiedSMTGen.EncoderSound

open Core Lambda Imperative Strata.SMT Std
open Core.Refactor
open Strata.SMT.DenoteTyped

namespace Core.Refactor.NonVacuityTest

/-- No name shorter than the 5-char reserved prefix `"$__bv"` can be a reserved binder id. -/
theorem name_not_reserved (s : String) (hs : s.length < 5) : ∀ n : Nat, s ≠ s!"$__bv{n}" := by
  intro n h
  have hl := congrArg String.length h
  rw [String.length_append] at hl
  have h2 : (toString "$__bv").length = 5 := by decide
  omega

/- ── The concrete obligation ─────────────────────────────────────────────── -/

def xi : Expression.Expr := .fvar () ⟨"x", ()⟩ (some .int)
def yi : Expression.Expr := .fvar () ⟨"y", ()⟩ (some .int)
def intTy : Expression.Ty := .forAll [] .int

/-- `havoc x; havoc y; assume x = x; distinct {x, y}; ⊢ y = y`. -/
def d : Imperative.ProofObligation Expression :=
  { label := "nonvacuity"
    property := .assert
    metadata := .empty
    assumptions := [[
      .varDecl ⟨"x", ()⟩ intTy .nondet,
      .varDecl ⟨"y", ()⟩ intTy .nondet,
      .assumption "h" (.eq () xi xi),
      .distinct "dxy" [xi, yi] ]]
    obligation := .eq () yi yi }

/-- A non-trivial factory: one user function `g : int → int` (bodyless / uninterpreted). -/
def g : LFunc CoreLParams :=
  { name := ⟨"g", ()⟩, inputs := [(⟨"a", ()⟩, (.int : LMonoTy))], output := (.int : LMonoTy) }
def F : Lambda.Factory CoreLParams := Factory.ofArray #[g]
/-- Empty type factory — no datatypes, so `datatypeOpNames tf = []`. -/
def tf : @Lambda.TypeFactory CoreLParams.IDMeta := TypeFactory.default

/- ── Well-formedness proofs ──────────────────────────────────────────────── -/

/-- The declared type `int` monomorphizes to `LMonoTy.int` (drives every `stepCtx` reduction). -/
theorem intTy_mono : LTy.toMonoType? intTy = some .int := by rfl

/-- A free `int` variable present in `Φ` is `int`-typed (for any function context `Ψ` — a nullary
    free-var head never consults `Ψ`). -/
theorem fvar_int {Φ : FVarCtx} {Ψ : FnCtx} {nm : String} (h : (nm, (.int : LMonoTy)) ∈ Φ) :
    LExpr.HasSimpType Φ Ψ [] (.fvar () ⟨nm, ()⟩ (some .int)) .int :=
  .fvarNullary ⟨nm, ()⟩ .int .int (.fvar ⟨nm, ()⟩ .int [] .int h rfl .int)

/-- The factory's user-function list is exactly `[g]` — recovered structurally (length 1 + the single
    element is `g` via `Factory.ofArray_mem`), avoiding the missing `DecidableEq (LFunc)`. -/
theorem F_nonPredefined : Factory.nonPredefined F tf = [g] := by
  have hlen : (Factory.nonPredefined F tf).length = 1 := by native_decide
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  have hmem : a ∈ Factory.nonPredefined F tf := by rw [ha]; exact List.mem_singleton.mpr rfl
  have haF : a ∈ F.toArray :=
    Array.mem_toList_iff.mp (List.mem_filter.mp (by rw [Factory.nonPredefined] at hmem; exact hmem)).1
  have hag : a = g := by simpa using Factory.ofArray_mem haF
  rw [ha, hag]

theorem F_factoryFnCtx : factoryFnCtx F tf = [("g", LMonoTy.mkArrow' .int [.int])] := by
  rw [factoryFnCtx, F_nonPredefined]; rfl

theorem F_fnames : (factoryFnCtx F tf).map Prod.fst = ["g"] := by rw [F_factoryFnCtx]; rfl

/-- The factory is simp-well-formed: `nonPredefined F tf = [g]`, so each clause reduces to a fact about
    `g` (the body clause is vacuous — `g` is bodyless; the axiom clause is vacuous — `g` has no axioms;
    the signature is base-typed with fresh, non-reserved names). -/
theorem hsimp : Factory.SimpWF F tf where
  fnsWF := by
    rw [F_nonPredefined]
    exact .cons (fun body _ hbody => by simp [g] at hbody) .nil
  fnAxiomsWF := by
    rw [F_nonPredefined]; intro f hf e he
    rcases List.mem_singleton.mp hf with rfl; simp [g] at he
  fnsSigSimp := by
    rw [F_nonPredefined]; intro f hf
    rcases List.mem_singleton.mp hf with rfl
    exact { fnRetBase := .int
            fnArgsBase := by intro a ha; simp [g, ListMap.values] at ha; subst ha; exact .int
            fnParamsWF := by simp [g, ListMap.keys]
            fnParamsFresh := by
              intro p hp; simp [g, ListMap.keys] at hp; subst hp; simp [F_fnames]
            fnNameNotReserved := name_not_reserved "g" (by decide) }

/-- The obligation is well-formed: its entries are order-well-typed and its goal is `bool`. -/
theorem hpwf : ProofObligation.WF F tf d where
  entriesWF := by
    show PathEntriesWF (factoryFnCtx F tf) [] _
    -- entry 1: havoc x
    refine PathEntriesWF.cons (.varDeclNondet (mty := .int) rfl .int ?_ (name_not_reserved "x" (by decide))) ?_
    · simp [F_factoryFnCtx]
    -- entry 2: havoc y  (Φ = [(x,int)])
    refine PathEntriesWF.cons (.varDeclNondet (mty := .int) rfl .int ?_ (name_not_reserved "y" (by decide))) ?_
    · simp [F_factoryFnCtx, stepCtx, intTy_mono]
    -- entry 3: assume x = x  (Φ = [(y,int),(x,int)])
    refine PathEntriesWF.cons (.assumption (.eq _ _ .int .int ?_ ?_)) ?_
    · exact fvar_int (by decide)
    · exact fvar_int (by decide)
    -- entry 4: distinct {x, y}
    refine PathEntriesWF.cons (.distinct (by decide) ⟨.int, .int, ?_⟩) PathEntriesWF.nil
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact fvar_int (by decide)
    · rcases List.mem_cons.mp he with rfl | he
      · exact fvar_int (by decide)
      · simp at he
  goalWF := by
    show LExpr.HasSimpType (accumFVarCtx _) (factoryFnCtx F tf) [] (.eq () yi yi) (.tcons "bool" [])
    exact .eq _ _ .int .int
      (fvar_int (by decide))
      (fvar_int (by decide))

/-- **The payoff.** For any query the encoder emits for `d`, if it `UnsatWithNegObl`, then `d` is valid. The
    WF preconditions are all discharged above (proving they are non-vacuous), so the headline theorem
    applies directly. -/
theorem d_valid_of_unsatWithNegObl {q : SMTQuery}
    (henc : encodeObligationRun false F tf [] d = .ok q)
    (hprove : q.UnsatWithNegObl
      (translateQuery_WF (collect_WF hpwf hsimp).1 (collect_WF hpwf hsimp).2 henc)) :
    ProofObligation.Valid F d hpwf hsimp :=
  obligation_valid_of_unsatWithNegObl hpwf hsimp henc hprove

end Core.Refactor.NonVacuityTest
