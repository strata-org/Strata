/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Encoder
import Strata.Languages.Core.Verifier

/-! ## Tests and proofs for Strata.Name.disambiguate / Strata.Name.breakDisambiguated -/

namespace Strata.SMT.Encoder

/-! ### Concrete roundtrip checks -/

#guard Strata.Name.breakDisambiguated (Strata.Name.disambiguate "x" 1) == ("x", 2)
#guard Strata.Name.breakDisambiguated (Strata.Name.disambiguate "x" 0) == ("x", 1)
#guard Strata.Name.breakDisambiguated (Strata.Name.disambiguate "foo" 42) == ("foo", 43)
#guard Strata.Name.breakDisambiguated (Strata.Name.disambiguate "$__bv0" 1) == ("$__bv0", 2)
-- Non-disambiguated names
#guard Strata.Name.breakDisambiguated "x" == ("x", 1)
#guard Strata.Name.breakDisambiguated "hello" == ("hello", 1)
-- Names with @ but no numeric suffix
#guard Strata.Name.breakDisambiguated "x@y" == ("x@y", 1)
-- Names with existing disambiguation
#guard Strata.Name.breakDisambiguated "x@1" == ("x", 2)

/-! ### Roundtrip proof -/

/-! #### Helper: digitChar properties -/

private theorem Nat.digitChar_val {n : Nat} (h : n < 10) :
    n.digitChar.toNat - '0'.toNat = n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

private theorem Nat.digitChar_isDigit {n : Nat} (h : n < 10) : n.digitChar.isDigit = true := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-! ### Structurally recursive digit generation

`Nat.toDigitsCore` uses `brecOn` (bounded recursion on Nat), which is hard to
reason about directly. We define an equivalent structurally recursive version
and prove it equal to `Nat.toDigitsCore`. -/

private def digitLoopFuel : Nat → Nat → List Char → List Char
  | 0, _, ds => ds
  | fuel + 1, n, ds =>
    let d := (n % 10).digitChar
    let n' := n / 10
    if n' = 0 then d :: ds else digitLoopFuel fuel n' (d :: ds)

private theorem digitLoopFuel_acc (fuel n : Nat) (ds : List Char) :
    digitLoopFuel fuel n ds = digitLoopFuel fuel n [] ++ ds := by
  induction fuel generalizing n ds with
  | zero => simp [digitLoopFuel]
  | succ fuel ih =>
    simp only [digitLoopFuel]; split
    · simp
    · rw [ih, ih (ds := [(n % 10).digitChar])]; simp [List.append_assoc]

private theorem digitLoopFuel_extra (fuel₁ fuel₂ n : Nat) (ds : List Char)
    (h₁ : fuel₁ > n) (h₂ : fuel₂ > n) :
    digitLoopFuel fuel₁ n ds = digitLoopFuel fuel₂ n ds := by
  induction n using Nat.strongRecOn generalizing fuel₁ fuel₂ ds with
  | _ n ih =>
    cases fuel₁ with
    | zero => omega
    | succ f₁ => cases fuel₂ with
      | zero => omega
      | succ f₂ =>
        simp only [digitLoopFuel]; split
        · rfl
        · exact ih (n / 10) (by omega) f₁ f₂ _ (by omega) (by omega)

/-! ### Bridge: digitLoopFuel = Nat.toDigitsCore -/

theorem digitLoopFuel_eq_toDigitsCore : ∀ (fuel n : Nat) (ds : List Char),
    digitLoopFuel fuel n ds = Nat.toDigitsCore 10 fuel n ds
  | 0, _, ds => by simp [digitLoopFuel, Nat.toDigitsCore]
  | fuel + 1, n, ds => by
    simp only [digitLoopFuel, Nat.toDigitsCore]; split
    · rfl
    · rw [digitLoopFuel_eq_toDigitsCore]

/-! ### All digits in Nat.repr are digit characters -/

private theorem digitLoopFuel_all_isDigit : ∀ (fuel n : Nat) (ds : List Char),
    ds.all Char.isDigit = true → (digitLoopFuel fuel n ds).all Char.isDigit = true
  | 0, _, _, hds => hds
  | fuel + 1, n, ds, hds => by
    simp only [digitLoopFuel]
    have hd := Nat.digitChar_isDigit (Nat.mod_lt n (by omega))
    split
    · simp [List.all_cons, hd, hds]
    · exact digitLoopFuel_all_isDigit fuel _ _ (by simp [List.all_cons, hd, hds])

theorem repr_digits_all_isDigit (n : Nat) :
    ∀ c ∈ n.repr.toList, c.isDigit = true := by
  rw [List.all_eq_true.symm, Nat.repr, String.toList_ofList, Nat.toDigits,
    ← digitLoopFuel_eq_toDigitsCore]
  exact digitLoopFuel_all_isDigit (n + 1) n [] (by simp)

/-! ### Reading back digits recovers the original number -/

private theorem readBack_digitLoopFuel (n : Nat) :
    List.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      (digitLoopFuel (n + 1) n []) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    simp only [digitLoopFuel]
    split
    · simp only [List.foldl]
      rw [Nat.digitChar_val (Nat.mod_lt n (by omega))]
      omega
    · rw [digitLoopFuel_acc, List.foldl_append, List.foldl]
      rw [Nat.digitChar_val (Nat.mod_lt n (by omega))]
      rw [digitLoopFuel_extra _ (n / 10 + 1) (n / 10) [] (by omega) (by omega)]
      rw [ih (n / 10) (by omega)]
      simp [List.foldl]
      omega

/-- `Strata.Name.digitsToNat` on the digits of `n` recovers `n`. -/
theorem digitsToNat_digitLoopFuel (n : Nat) :
    Strata.Name.digitsToNat (digitLoopFuel (n + 1) n []) = n :=
  readBack_digitLoopFuel n

/-- `Nat.repr n` is non-empty. -/
private theorem digitLoopFuel_ne_nil (n : Nat) : digitLoopFuel (n + 1) n [] ≠ [] := by
  simp only [digitLoopFuel]
  split
  · simp
  · rw [digitLoopFuel_acc]; simp

private theorem repr_toList_ne_nil (n : Nat) : n.repr.toList ≠ [] := by
  simp only [Nat.repr, String.toList_ofList, Nat.toDigits, ← digitLoopFuel_eq_toDigitsCore]
  exact digitLoopFuel_ne_nil n

/-! ### Helper lemmas for the main roundtrip proof -/

private theorem List.takeWhile_eq_of_all {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = true) : List.takeWhile p xs = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.takeWhile, h x (.head xs), ih (fun y hy => h y (.tail x hy))]

private theorem List.dropWhile_eq_nil_of_all {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = true) : List.dropWhile p xs = [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.dropWhile, h x (.head xs), ih (fun y hy => h y (.tail x hy))]

set_option linter.deprecated false in
private theorem String.mk_eq_ofList (cs : List Char) : String.mk cs = String.ofList cs := rfl

/-! ### Main roundtrip theorem -/

set_option linter.unusedSimpArgs false

/-- Breaking a disambiguated name recovers the base name and incremented suffix,
    provided the base name does not contain `@`. -/
theorem breakDisambiguated_disambiguate (baseName : String) (n : Nat)
    (_h : ¬ baseName.any (· == '@')) :
    Strata.Name.breakDisambiguated (Strata.Name.disambiguate baseName n) = (baseName, n + 1) := by
  simp only [Strata.Name.disambiguate, Strata.Name.breakDisambiguated,
    Strata.Name.digitsToNat,
    toString, String.toList_append,
    List.reverse_append, List.append_assoc]
  have hat : "@".toList.reverse = ['@'] := by native_decide
  rw [hat]
  have hdigrev : ∀ c ∈ n.repr.toList.reverse, Char.isDigit c = true :=
    fun c hc => repr_digits_all_isDigit n c (List.mem_reverse.mp hc)
  simp only [List.takeWhile_append, List.takeWhile_eq_of_all hdigrev,
    List.dropWhile_append, List.dropWhile_eq_nil_of_all hdigrev,
    List.isEmpty, List.dropWhile, List.takeWhile,
    show Char.isDigit '@' = false from by native_decide,
    ite_true, List.nil_append, List.reverse_reverse,
    show (false = true) = False from by simp,
    show (0 = 0 + 1) = False from by simp,
    ite_false, List.append_nil, List.cons_append]
  -- digitSuffix = n.repr.toList (non-empty), rest.reverse = '@' :: baseName.toList.reverse
  -- Match on ('@' :: _, _ :: _) succeeds since n.repr.toList is non-empty
  have hne : n.repr.toList ≠ [] := repr_toList_ne_nil n
  match h : n.repr.toList with
  | [] => exact absurd h hne
  | c :: cs =>
    simp only []
    -- Strata.Name.digitsToNat (c :: cs) = Strata.Name.digitsToNat n.repr.toList = n
    -- via digitLoopFuel bridge
    simp only [Strata.Name.digitsToNat,
      Nat.repr, String.toList_ofList, Nat.toDigits,
      ← digitLoopFuel_eq_toDigitsCore] at h
    rw [← h, readBack_digitLoopFuel]
    simp only [List.reverse_cons, List.reverse_reverse, List.dropLast_concat,
      String.mk_eq_ofList, String.ofList_toList]

end Strata.SMT.Encoder

/-! ## Tests for unified `usedNames` registry (issue #1230)

Verifies that the encoder disambiguates when a user-defined UF name collides
with the internal `f.N` naming scheme used by `encodeFunction`, and when
UF names collide with pre-declared sort/datatype names. -/

namespace Strata.SMT.Encoder.UsedNamesTests

open Strata.SMT

/-- Helper: run an `EncoderM` action against a buffer solver and return the
    final encoder state. -/
private def runEncoder (act : EncoderM Unit) : IO EncoderState := do
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Solver.bufferWriter b
  let (((), estate), _) ← (act.run EncoderState.init).run solver
  return estate

/-- Helper: run an `EncoderM` action with a pre-populated state. -/
private def runEncoderWith (initState : EncoderState) (act : EncoderM Unit) : IO EncoderState := do
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Solver.bufferWriter b
  let (((), estate), _) ← (act.run initState).run solver
  return estate

-- A user UF named `f.0` should not collide with the first `encodeFunction`
-- output. The encoder must rename one of them.
/-- info: ("f.0", "f.1") -/
#guard_msgs in
#eval do
  let collidingUF : UF := { id := "f.0", args := [], out := .int }
  let functionUF : UF := { id := "userFn", args := [⟨"x", .int⟩], out := .int }
  let body : Term := .var ⟨"x", .int⟩
  let estate ← runEncoder do
    let _ ← Encoder.encodeUF collidingUF
    let _ ← Encoder.encodeFunction functionUF body
  return (estate.ufs[collidingUF]!, estate.ufs[functionUF]!)

-- A user UF named `f.1` should not collide when two functions are encoded.
/-- info: ("f.1", "f.1@1", "f.2") -/
#guard_msgs in
#eval do
  let collidingUF : UF := { id := "f.1", args := [], out := .bool }
  let fn0 : UF := { id := "fn0", args := [], out := .int }
  let fn1 : UF := { id := "fn1", args := [⟨"y", .int⟩], out := .int }
  let body0 : Term := .prim (.int 42)
  let body1 : Term := .var ⟨"y", .int⟩
  let estate ← runEncoder do
    let _ ← Encoder.encodeUF collidingUF
    let _ ← Encoder.encodeFunction fn0 body0
    let _ ← Encoder.encodeFunction fn1 body1
  return (estate.ufs[collidingUF]!, estate.ufs[fn0]!, estate.ufs[fn1]!)

-- A UF named the same as a pre-declared datatype/sort should be disambiguated
-- when the encoder state is initialized with those names.
/-- info: "MyDatatype@1" -/
#guard_msgs in
#eval do
  let preDeclaredNames := Std.HashSet.ofList ["MyDatatype", "Option"]
  let uf : UF := { id := "MyDatatype", args := [], out := .int }
  let estate ← runEncoderWith (EncoderState.initWithNames preDeclaredNames) do
    let _ ← Encoder.encodeUF uf
  return estate.ufs[uf]!

-- A function whose generated name collides with a pre-declared sort should
-- also be disambiguated.
/-- info: "f.0@1" -/
#guard_msgs in
#eval do
  let preDeclaredNames := Std.HashSet.ofList ["f.0"]
  let fn : UF := { id := "userFn", args := [⟨"x", .int⟩], out := .int }
  let body : Term := .var ⟨"x", .int⟩
  let estate ← runEncoderWith (EncoderState.initWithNames preDeclaredNames) do
    let _ ← Encoder.encodeFunction fn body
  return estate.ufs[fn]!

-- A UF named identically to a constructor declared via `declareType` should
-- be disambiguated.
/-- info: ("MyConstr@1", "MyConstr") -/
#guard_msgs in
#eval do
  let uf : UF := { id := "MyConstr", args := [], out := .int }
  let estate ← runEncoder do
    let _ ← Encoder.declareType "MyType" ["MyConstr", "OtherConstr"]
    let _ ← Encoder.encodeUF uf
  return (estate.ufs[uf]!, "MyConstr")

-- A UF named `Option` (or `none`/`some`/`val`) should be disambiguated against
-- the built-in Option datatype names pre-populated in `encode`.
/-- info: ("Option@1", "none@1", "some@1", "val@1") -/
#guard_msgs in
#eval do
  let ufOption : UF := { id := "Option", args := [], out := .int }
  let ufNone : UF := { id := "none", args := [], out := .int }
  let ufSome : UF := { id := "some", args := [], out := .int }
  let ufVal : UF := { id := "val", args := [], out := .int }
  let initState := EncoderState.initWithNames (Std.HashSet.ofList ["Option", "none", "some", "val"])
  let estate ← runEncoderWith initState do
    let _ ← Encoder.encodeUF ufOption
    let _ ← Encoder.encodeUF ufNone
    let _ ← Encoder.encodeUF ufSome
    let _ ← Encoder.encodeUF ufVal
  return (estate.ufs[ufOption]!, estate.ufs[ufNone]!, estate.ufs[ufSome]!, estate.ufs[ufVal]!)

end Strata.SMT.Encoder.UsedNamesTests

/-! ## Tests for AbstractEncoder paths (issue #1230)

Verifies that `AbstractEncoder.encodeUF` and `AbstractEncoder.encodeFunction`
use the same `uniquify` logic as the batch encoder. -/

namespace Strata.SMT.Encoder.AbstractEncoderTests

open Strata.SMT
open Strata.SMT.Encoder

/-- Minimal mock solver that records declared names. We only need `declareFun`
    and `defineFun` to exercise the AbstractEncoder's uniquify logic. -/
private abbrev MockM := ExceptT IO.Error (StateM (List String))

private def mockSolver : AbstractSolver String String MockM where
  setLogic _ := pure ()
  setOption _ _ := pure ()
  comment _ := pure ()
  boolSort := pure "Bool"
  intSort := pure "Int"
  realSort := pure "Real"
  stringSort := pure "String"
  regexSort := pure "RegLan"
  bitvecSort n := pure s!"(_ BitVec {n})"
  arraySort k v := pure s!"(Array {k} {v})"
  constrSort name _ := pure name
  mkBool b := pure (toString b)
  mkInt i := pure (toString i)
  mkPrim _ := pure "prim"
  mkAppOp _ _ _ := pure "app"
  mkAnd _ := pure "and"
  mkOr _ := pure "or"
  mkNot _ := pure "not"
  mkImplies _ _ := pure "implies"
  mkAdd _ := pure "add"
  mkSub _ := pure "sub"
  mkMul _ := pure "mul"
  mkDiv _ _ := pure "div"
  mkMod _ _ := pure "mod"
  mkNeg _ := pure "neg"
  mkAbs _ := pure "abs"
  mkEq _ := pure "eq"
  mkLt _ := pure "lt"
  mkLe _ := pure "le"
  mkGt _ := pure "gt"
  mkGe _ := pure "ge"
  mkIte _ _ _ := pure "ite"
  mkSelect _ _ := pure "select"
  mkStore _ _ _ := pure "store"
  mkApp _ _ := pure "app"
  mkForall _ cb := do let (body, _) ← cb []; pure body
  mkExists _ cb := do let (body, _) ← cb []; pure body
  declareNew name _ := pure name
  declareFun name _ _ := do modify (· ++ [name]); pure name
  defineFun name _ _ _ := modify (· ++ [name])
  declareSort name _ := pure name
  declareDatatype name _ _ := pure { sort := name, constructors := [] }
  declareDatatypes headers _ := pure (headers.map fun (n, _) => { sort := n, constructors := [] })
  assert _ := pure ()
  checkSat := pure .unsat
  checkSatAssuming _ := pure .unsat
  getUnsatAssumptions := pure []
  getModel := pure []
  getValue _ := pure []
  termToSMTLibString t := pure t
  reset := pure ()
  close := pure ()

/-- Run an AbstractEncoderM action with a pre-populated state and return the
    final base encoder state. -/
private def runAbstractEncoder (initNames : Std.HashSet String)
    (act : AbstractEncoderM String MockM Unit) : EncoderState :=
  let initState : AbstractEncoderState String := { base := EncoderState.initWithNames initNames }
  let result := ((act.run initState).run).run []
  match result with
  | (.ok ((), st), _) => st.base
  | (.error _, _) => EncoderState.init

-- AbstractEncoder.encodeUF disambiguates against pre-declared names
/-- info: "f.0@1" -/
#guard_msgs in
#eval do
  let preDeclaredNames := Std.HashSet.ofList ["f.0"]
  let uf : UF := { id := "f.0", args := [], out := .int }
  let estate := runAbstractEncoder preDeclaredNames do
    let _ ← AbstractEncoder.encodeUF mockSolver uf
  return estate.ufs[uf]!

-- AbstractEncoder.encodeFunction disambiguates against pre-declared names
/-- info: "f.0@1" -/
#guard_msgs in
#eval do
  let preDeclaredNames := Std.HashSet.ofList ["f.0"]
  let fn : UF := { id := "userFn", args := [⟨"x", .int⟩], out := .int }
  let body : Term := .var ⟨"x", .int⟩
  let estate := runAbstractEncoder preDeclaredNames do
    let _ ← AbstractEncoder.encodeFunction mockSolver fn body
  return estate.ufs[fn]!

-- AbstractEncoder: UF-vs-function collision (same as batch path)
/-- info: ("f.0", "f.1") -/
#guard_msgs in
#eval do
  let collidingUF : UF := { id := "f.0", args := [], out := .int }
  let functionUF : UF := { id := "userFn", args := [⟨"x", .int⟩], out := .int }
  let body : Term := .var ⟨"x", .int⟩
  let estate := runAbstractEncoder {} do
    let _ ← AbstractEncoder.encodeUF mockSolver collidingUF
    let _ ← AbstractEncoder.encodeFunction mockSolver functionUF body
  return (estate.ufs[collidingUF]!, estate.ufs[functionUF]!)

end Strata.SMT.Encoder.AbstractEncoderTests
