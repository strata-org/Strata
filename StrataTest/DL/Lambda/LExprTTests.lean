/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.LExprT

meta section
namespace Lambda
---------------------------------------------------------------------
open Std (ToFormat Format format)
open LTy

section Tests

open LTy.Syntax LExpr.SyntaxMono LExpr LMonoTy

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()

/-- info: error: Cannot infer the type of this bvar: %2 -/
#guard_msgs in
-- Ill-formed terms, like those that contain dangling bound variables, do not
-- type check.
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default
                             esM[λλ %2]
         return (format $ ans)

/-- info: ok: (((λ (%0 : $__ty3)) : (arrow $__ty3 $__ty3)) (y : $__ty3)) : $__ty3) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default (TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("y", t[∀x. %x])]] })
                            esM[((λ %0) y)]
         return (format $ ans.fst)

/-- info: error: Impossible to unify bool with int. -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default (TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("x", t[bool])]] })
                         esM[if #true then (x == #5) else (x == #6)]
         return format ans

/-- info: ok: (if #true then ((x : int) == #5) else ((x : int) == #6)) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate (T:=TestParams) LContext.default (TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("x", t[∀x. %x])]] })
                               esM[if #true then (x == #5) else (x == #6)]
         return (format $ ans.fst)

/-- info: ok: (λ (bvar:$__ty0) %0) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate (T:=TestParams) LContext.default TEnv.default esM[λ(%0)]
         return format ans.fst

/-- info: ok: (∀ (bvar:int) (%0 == #5)) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate (T:=TestParams) LContext.default TEnv.default esM[∀ (%0 == #5)]
         return format ans.fst

/-- info: ok: (λ (bvar:int) ((succ : (arrow int int)) %0)) -/
#guard_msgs in
#eval do let ans ← LExpr.annotate (T:=TestParams) LContext.default ( TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("succ", t[int → int])]] })
                               esM[λ(succ %0)]
         return (format $ ans.fst)

/-- info: ok: (∀(int) ((%0 : int) == (#5 : int)) : bool)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[∀ (%0 == #5)]
         return (format $ ans.fst)

-- An unannotated quantifier binder whose body is the bound variable itself:
-- the body's fresh type variable is unified with `bool`, so the binder is
-- inferred to have type `bool`.
/-- info: ok: (∀(bool) (%0 : bool)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[∀ %0]
         return (format $ ans.fst)

-- A quantifier body that is genuinely non-Boolean (here `#5 : int`) is rejected
-- because its type cannot unify with `bool`.
/-- info: error: Impossible to unify int with bool. -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[∀ #5]
         return (format $ ans.fst)

-- Nested quantifiers: the inner body must unify to `bool`, and the substitution
-- threads through both binder layers. The unused outer binder stays a fresh
-- type variable.
/-- info: ok: (∀($__ty0) (∀(bool) (%0 : bool))) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[∀ (∀ %0)]
         return (format $ ans.fst)

/-- info: ok: ((λ (%0 : $__ty0)) : (arrow $__ty0 $__ty0)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[λ(%0)]
         return (LExprT.format $ ans.fst)

-- Resolving a `have` binding: `have x = #5 in (x == #5)`.
/-- info: ok: (((λ ((%0 : int) == (#5 : int)) : bool)) : (arrow int bool)) (#5 : int)) : bool) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default
                     (LExpr.mkHave () "x" none esM[#5] esM[%0 == #5])
         return (LExprT.format $ ans.fst)

-- Same, with the binder explicitly annotated: `have x : int = #5 in (x == #5)`.
/-- info: ok: (((λ ((%0 : int) == (#5 : int)) : bool)) : (arrow int bool)) (#5 : int)) : bool) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default
                     (LExpr.mkHave () "x" (some mty[int]) esM[#5] esM[%0 == #5])
         return (LExprT.format $ ans.fst)

/-- info: ok: (#5 : int) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[#5]
         return (LExprT.format $ ans.fst)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[((λ %0) #5)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow $__ty0 int) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[λ #5]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow (arrow int $__ty2) $__ty2) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[λ(%0 #5)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow $__ty0 (arrow (arrow $__ty0 $__ty4) $__ty4)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[λλ(%0 %1)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow (arrow int $__ty4) $__ty4) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default esM[((λλ (%0 %1)) #5)]
         return (format ans.fst.toLMonoTy)

/--
info: error: Failed occurs check: $__ty0 cannot be unified with (arrow $__ty0 $__ty3) because it would create a circular dependency during unification.
-/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default
                            esM[λ(%0 %0)]
         return (format $ ans.fst)

/-- info: ok: (arrow (arrow $__ty6 $__ty7) (arrow (arrow $__ty2 $__ty6) (arrow $__ty2 $__ty7))) -/
#guard_msgs in
-- Term: fun f -> (fun g -> (fun x -> (f (g x))))
-- Expected type: ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default
                            esM[λλλ(%2 (%1 %0))]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow (arrow $__ty6 $__ty6) (arrow $__ty6 $__ty6)) -/
#guard_msgs in
-- Term: fun f -> (fun x -> (f (f x)))
-- Expected type: ('a -> 'a) -> 'a -> 'a
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default
                            esM[λλ (%1 (%1 %0))]
         return (format $ ans.fst.toLMonoTy)

/--
info: ok: (arrow (arrow $__ty2 (arrow $__ty8 $__ty9)) (arrow (arrow $__ty2 $__ty8) (arrow $__ty2 $__ty9)))
-/
#guard_msgs in
-- Function: fun f -> (fun g -> (fun x -> ((f x) (g x))))
-- Expected type: ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default
                            esM[λλλ ((%2 %0) (%1 %0))]
         return (format $ ans.fst.toLMonoTy)

/--
info: error: Failed occurs check: $__ty1 cannot be unified with (arrow $__ty1 $__ty5) because it would create a circular dependency during unification.
-/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default
                            esM[λλ(%1 (%0 %0))]
         return (format $ ans.fst)

private def testIntFns : (Factory TestParams) := .ofArray
  #[{ name := "unit",
      inputs := [],
      output := mty[unit]},
    { name := "Int.Add",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int]},
    { name := "Int.Div",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int]},
    { name := "Int.Neg",
      inputs := [("x", mty[int])],
      output := mty[int]},
    { name := "SynonymTest",
      inputs := [("x", mty[myInt]), ("y", mty[int])],
      output := mty[int]}
  ]

/--
info: error: Type unit is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), string, int, bool]
-/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) {LContext.default with functions := testIntFns} TEnv.default
                             esM[~unit]
         return (format $ ans.fst)

/-- info: ok: (~unit : unit) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) { LContext.default with functions := testIntFns, knownTypes := makeKnownTypes [t[unit].toKnownType!] } TEnv.default
                             esM[~unit]
         return (format $ ans.fst)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) {LContext.default with functions := testIntFns}
                    ((@TEnv.default TestParams.IDMeta).updateContext { aliases := [{typeArgs := [], name := "myInt", type := mty[int]}]})
                             esM[((~SynonymTest #20) #30)]
         return (format $ ans.fst.toLMonoTy)

/--
info: error: Impossible to unify (arrow int int) with (arrow bool $__ty0).
First mismatch: int with bool.
-/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) { LContext.default with functions := testIntFns } TEnv.default
                             esM[(~Int.Neg #true)]
         return (format $ ans)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) { LContext.default with functions := testIntFns } TEnv.default
                             esM[(~Int.Neg #100)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) { LContext.default with functions := testIntFns } TEnv.default
                             esM[((λ %0) ((~Int.Add #20) #30))]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) {LContext.default with functions := testIntFns} ((@TEnv.default TestParams.IDMeta).updateContext { types := Strata.Util.HMaps.ofScopes [[("x", t[int])]] })
                             esM[(λ (~Int.Add %0))]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) {LContext.default with functions := testIntFns} ((@TEnv.default TestParams.IDMeta).updateContext { types := Strata.Util.HMaps.ofScopes [[("x", t[int])]] })
                             esM[λλ ((~Int.Add %0) %1)]
         return (format $ ans.fst.toLMonoTy)

/-- info: ok: (arrow int (arrow int int)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) {LContext.default with functions := testIntFns} ((@TEnv.default TestParams.IDMeta).updateContext { types := Strata.Util.HMaps.ofScopes [[("x", t[int])]] })
                             esM[(λλ ((~Int.Add %1) %0))]
         return (format $ ans.fst.toLMonoTy);

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) {LContext.default with functions := testIntFns} ((@TEnv.default TestParams.IDMeta).updateContext { types := Strata.Util.HMaps.ofScopes [[("x", t[int])]] })
                             esM[((~Int.Add x) (~Int.Neg #30))]
         return (format $ ans.fst.toLMonoTy)

/--
info: ok: ((~Int.Add : (arrow int (arrow int int))) (x : int) ((~Int.Neg : (arrow int int)) #30))
-/
#guard_msgs in
#eval do let ans ← LExpr.annotate (T:=TestParams) {LContext.default with functions := testIntFns} ((@TEnv.default TestParams.IDMeta).updateContext { types := Strata.Util.HMaps.ofScopes [[("x", t[int])]] })
                                   esM[((~Int.Add x) (~Int.Neg #30))]
         return (format $ ans.fst)

/--
info: ok: ((λ ((%0 : (arrow bool $__ty4)) ((fn : (arrow bool bool)) (#true : bool)) : bool)) : $__ty4)) : (arrow (arrow bool $__ty4) $__ty4))
-/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) {LContext.default with functions := testIntFns} ((@TEnv.default TestParams.IDMeta).updateContext { types := Strata.Util.HMaps.ofScopes [[("fn", t[∀a. %a → %a])]] })
                             esM[(λ (%0 (fn #true)))]
         return format ans.fst

/-- info: ok: int -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) {LContext.default with functions := testIntFns} ((@TEnv.default TestParams.IDMeta).updateContext { types := Strata.Util.HMaps.ofScopes [[("fn", t[∀a. %a → %a])]] })
                             esM[(fn #3)]
         return (format $ ans.fst.toLMonoTy)

/-! ### Opening a binder never captures a free variable of its body

Each body mentions a free variable named `$__var0`, the first name the
generator would pick for the bound variable. -/

/-- The syntax tree `λ x. x == $__var0`. -/
private def bodyMentionsGenName : LExpr TestParams.mono :=
  .abs () "x" none (.eq () (.bvar () 0) (.fvar () ⟨"$__var0", ()⟩ none))

-- With `$__var0` unbound, the program is ill-scoped and must be rejected: the
-- generator skips `$__var0`, so the body's `$__var0` is not mistaken for the
-- bound variable.
/-- info: error: Cannot find this fvar in the context! $__var0 -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default TEnv.default bodyMentionsGenName
         return (LExprT.format $ ans.fst)

-- With `$__var0 : int` in the context, the program is well-scoped: the bound
-- variable gets a different name and `$__var0` stays free in the result.
/-- info: ok: ((λ ((%0 : int) == ($__var0 : int)) : bool)) : (arrow int bool)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default
                     (TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("$__var0", t[int])]] })
                     bodyMentionsGenName
         return (LExprT.format $ ans.fst)

-- The same holds for a quantifier body.
/-- info: ok: (∀(int) ((%0 : int) == ($__var0 : int)) : bool)) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default
                     (TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("$__var0", t[int])]] })
                     (.quant () .all "x" none (LExpr.noTrigger ())
                       (.eq () (.bvar () 0) (.fvar () ⟨"$__var0", ()⟩ none)))
         return (LExprT.format $ ans.fst)

-- Nested binders: when the inner binder is opened, the outer one is already a
-- generated free variable of the inner body, so the inner binder avoids both it
-- and `$__var0`. The term is `λ x. λ y. (x == $__var0) == (y == $__var0)`.
/-- info: ok: ((λ ((λ (((%1 : int) == ($__var0 : int)) : bool) == ((%0 : int) == ($__var0 : int)) : bool)) : bool)) : (arrow int bool))) : (arrow int (arrow int bool))) -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default
                     (TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("$__var0", t[int])]] })
                     (.abs () "x" (some mty[int]) (.abs () "y" (some mty[int])
                       (.eq () (.eq () (.bvar () 1) (.fvar () ⟨"$__var0", ()⟩ none))
                               (.eq () (.bvar () 0) (.fvar () ⟨"$__var0", ()⟩ none)))))
         return (LExprT.format $ ans.fst)

-- And for a quantifier where only the trigger mentions `$__var0`: the
-- resolved trigger still refers to the free variable.
/-- info: ok: [$__var0] -/
#guard_msgs in
#eval do let ans ← LExpr.resolve (T:=TestParams) LContext.default
                     (TEnv.default.updateContext { types := Strata.Util.HMaps.ofScopes [[("$__var0", t[int])]] })
                     (.quant () .all "x" (some mty[int]) (.fvar () ⟨"$__var0", ()⟩ none)
                       (.eq () (.bvar () 0) (.bvar () 0)))
         return (format $ ans.fst.unresolved.freeVars.map (fun (x : TestParams.Identifier × Option LMonoTy) => x.1.name))

/-- `n` nested quantifiers `∀ x : int. … ∀ x : int. x == x`. -/
private def nestedQuants : Nat → LExpr TestParams.mono
  | 0 => .eq () (.bvar () 0) (.bvar () 0)
  | n + 1 => .quant () .all "x" (some mty[int]) (LExpr.noTrigger ()) (nestedQuants n)

/-- The resolved form of `nestedQuants n`: `n` quantifiers over `int` around a
    Boolean `%0 == %0`. -/
private def isResolvedNestedQuants : Nat → LExprT TestParams.mono → Bool
  | 0, .eq m (.bvar _ 0) (.bvar _ 0) => m.type == mty[bool]
  | n + 1, .quant _ .all _ (some ty) _ body => ty == mty[int] && isResolvedNestedQuants n body
  | _, _ => false

-- Each binder computes its body's free variables, so type checking costs
-- O(depth × size) in the nesting depth. Two hundred nested quantifiers must
-- still type check to the expected term well within a generous bound (10 s), so
-- a regression past that cost shows up here.
/-- info: ok within bound -/
#guard_msgs in
#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  let r := LExpr.resolve (T:=TestParams) LContext.default TEnv.default (nestedQuants 200)
  let ok : Bool := match r with | .ok (et, _) => isResolvedNestedQuants 200 et | .error _ => false
  let t1 ← IO.monoMsNow
  IO.println (if ok && t1 - t0 < 10000 then "ok within bound" else s!"failed or slow: {t1 - t0} ms")

end Tests

---------------------------------------------------------------------

end Lambda
end
