/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.TestGen

/-! ## Tests for TestGen -/

namespace Lambda
open Plausible
open LTy
open TestGen

#guard_msgs(drop info) in
#eval
  let P : String → Prop := fun s => s.isInt
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: 2 -/
#guard_msgs(info) in
#eval
  let P : Nat → Prop := fun n : Nat => MapFind [((2 : Nat), "foo")] n "foo"
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: 2 -/
#guard_msgs(info) in
#eval
  let P : Nat → Prop := fun n : Nat => MapsFind [[((2 : Nat), "foo")]] n "foo"
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: "foo" -/
#guard_msgs(info) in
#eval
  let P : String → Prop := fun s : String => MapFind [((2 : Nat), "foo")] 2 s
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

#guard_msgs(drop info) in
#eval
  let ty := .forAll [] (LMonoTy.bool)
  let ctx : TContext TrivialParams.IDMeta := ⟨[[(⟨"foo", ()⟩, ty)]], []⟩
  let P : TyIdentifier → Prop := fun s : String => TContext.isFresh s ctx
  Gen.runUntil .none (@ArbitrarySizedSuchThat.arbitrarySizedST _ P (@instArbitrarySizedSuchThatFresh _ _ ctx) 10) 10

/-- info: false -/
#guard_msgs(info) in
#eval DecOpt.decOpt (MapNotFound [("foo", 4)] "foo") 5
/-- info: true -/
#guard_msgs(info) in
#eval DecOpt.decOpt (MapNotFound [("foo", 4)] "bar") 5

/-- info: [(2, "new")] -/
#guard_msgs(info) in
#eval
  let P : Map Nat String → Prop := fun m' => MapReplace [((2 : Nat), "old")] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: false -/
#guard_msgs(info) in
#eval DecOpt.decOpt (MapsNotFound [[("foo", 4)]] "foo") 5
/-- info: true -/
#guard_msgs(info) in
#eval DecOpt.decOpt (MapsNotFound [[("foo", 4)]] "bar") 5

/-- info: [[(2, "new")]] -/
#guard_msgs(info) in
#eval
  let P : Maps Nat String → Prop := fun m' => MapsReplace [[((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: "old" -/
#guard_msgs(info) in
#eval
  let P : _ → Prop := fun z => MapsFind [[((2 : Nat), "old")]] 2 z
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: [[(2, "new")]] -/
#guard_msgs(info) in
#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: [[], [(2, "new")]] -/
#guard_msgs(info) in
#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[], [((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: [[(2, "new")], [(3, "old")]] -/
#guard_msgs(info) in
#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[], [((3 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: (3, "old") -/
#guard_msgs(info) in
#eval
  let P : _ → Prop := fun m => MapsFind₂ [[], [((3 : Nat), "old")]] m
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- error: Generation failure:Gen.runUntil: Out of attempts
-/
#guard_msgs(error) in
#eval
  let P : String × Nat → Prop := fun m => MapsFind₂ [[], []] m
  Gen.runUntil (.some 10) (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

#guard_msgs(drop info) in
#eval Gen.printSamples (Arbitrary.arbitrary : Gen LMonoTy)

abbrev example_lctx : LContext TrivialParams :=
{ LContext.empty with knownTypes := KnownTypes.default
                      functions := Lambda.IntBoolFactory
}

abbrev example_ctx : TContext Unit := ⟨[[]], []⟩
abbrev example_ty : LTy := .forAll [] <| .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]

/-- info: [[({ name := "y", metadata := () }, Lambda.LTy.forAll [] (Lambda.LMonoTy.tcons "int" []))]] -/
#guard_msgs(info) in
#eval
  let P : Maps (Identifier Unit) LTy → Prop := fun Γ => MapsInsert (example_ctx.types) "y" (.forAll [] (.tcons "int" [])) Γ
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5

#guard_msgs(drop info) in
#time #eval
    let P : LExpr TrivialParams.mono → Prop := fun t => HasType example_lctx example_ctx t example_ty
    Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 4) 4

/-- info: [LExpr.fvar () { name := "x", metadata := () } none, LExpr.fvar () { name := "y", metadata := () } none] -/
#guard_msgs(info) in
#eval Shrinkable.shrink (LExpr.eq (T := TrivialParams.mono) () (.fvar () "x" .none) (.fvar () "y" .none))

/-- info: 2 -/
#guard_msgs(info) in
#eval shrinkFun (fun n : Nat => n % 3 == 2) 42

#guard_msgs(drop info) in
#eval Strata.Util.withStdGenSeed 0 do
    let P : LExpr TrivialParams.mono → Prop := fun t => HasType example_lctx example_ctx t example_ty
    let t ← Gen.runUntil (.some 10) (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    IO.println s!"Generated {t}"

/-- info: Generating terms of type
Lambda.LTy.forAll [] (Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.tcons "bool" [], Lambda.LMonoTy.tcons "bool" []])
in context
{ types := [[]], aliases := [] }
in factory
#[Int.Add, Int.Sub, Int.Mul, Int.Div, Int.Mod, Int.Neg, Int.Lt, Int.Le, Int.Gt, Int.Ge, Bool.And, Bool.Or, Bool.Implies, Bool.Equiv, Bool.Not]
-/
#guard_msgs in
#eval Strata.Util.withStdGenSeed 0 do
  IO.println s!"Generating terms of type\n{example_ty}\nin context\n{repr example_ctx}\nin \
                factory\n{example_lctx.functions.map (fun f : LFunc TrivialParams => f.name)}\n"
  for i in List.range 100 do
    let P : LExpr TrivialParams.mono → Prop := fun t => HasType example_lctx example_ctx t example_ty
    let t ← Gen.runUntil (.some 1000) (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    if !(canAnnotate t) then
      let .error e := annotate t | throw <| IO.Error.userError "Unreachable"
      IO.println s!"FAILED({i}): {e}\n{t}\n\nSHRUNK TO:\n{shrinkFun (not ∘ canAnnotate) t}\n\n"

/-- info: Generating terms of type
Lambda.LTy.forAll [] (Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.tcons "bool" [], Lambda.LMonoTy.tcons "bool" []])
in context
{ types := [[]], aliases := [] }
in factory
#[Int.Add, Int.Sub, Int.Mul, Int.Div, Int.Mod, Int.Neg, Int.Lt, Int.Le, Int.Gt, Int.Ge, Bool.And, Bool.Or, Bool.Implies, Bool.Equiv, Bool.Not]
-/
#guard_msgs(info, drop error) in
#eval Strata.Util.withStdGenSeed 0 do
  IO.println s!"Generating terms of type\n{example_ty}\nin context\n{repr example_ctx}\nin \
                factory\n{example_lctx.functions.map (fun f : LFunc _ => f.name)}\n"
  for _i in List.range 100 do
    let P : LExpr TrivialParams.mono → Prop := fun t => HasType example_lctx example_ctx t (.forAll [] (.tcons "int" []))
    let t ← Gen.runUntil (.some 1000) (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    if !(reduces t) then
      continue

end Lambda
