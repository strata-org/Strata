/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.LTy
import Strata.DL.SMT.Term
import Strata.DL.SMT.Encoder
import Strata.Languages.Core.Env
import Strata.Languages.Core.Factory
import Strata.Languages.Core.Identifiers
import Strata.Languages.Core.Options
import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.Verifier
import Strata.DL.Lambda.TestGen
import Strata.DL.Lambda.PlausibleHelpers
import Plausible.Gen

/-! This file does random testing of Strata Core operations registered in factory, by
(1) choosing random constant inputs to the operations
(2) doing concrete evaluation and getting the results,
(3) SMT encoding the expression, and
(4) checking using the SMT solver whether the concrete output is equal to
the SMT expression.
-/

namespace Core

section Tests

open Lambda
open Std

def encode (e:LExpr CoreLParams.mono)
           (tenv:TEnv Visibility)
           (init_state:LState CoreLParams):
    Except Format (Option (Strata.SMT.Term × SMT.Context))
  := do
  let init_state ← init_state.addFactory Core.Factory |>.mapError (fun dm => f!"{dm.message}")
  let lcont := { Lambda.LContext.default with
    functions := Core.Factory, knownTypes := Core.KnownTypes }
  let (e,_T) ← LExpr.annotate lcont tenv e
  let e_res := LExpr.eval init_state.config.fuel init_state e
  match e_res with
  | .const _ _ =>
    let env := Core.Env.init
    let (smt_term_lhs,ctx) ← Core.toSMTTerm env [] e SMT.Context.default
    let (smt_term_rhs,ctx) ← Core.toSMTTerm env [] e_res ctx
    let smt_term_eq := Strata.SMT.Factory.eq smt_term_lhs smt_term_rhs
    return (.some (smt_term_eq, ctx))
  | _ => return .none

/--
Check whether concrete evaluation of e matches the SMT encoding of e.
Returns false if e did not reduce to a constant.
-/
def checkValid (e:LExpr CoreLParams.mono): IO Bool := do
  let tenv := TEnv.default
  let init_state := LState.init
  match encode e tenv init_state with
  | .error msg => throw (IO.userError s!"error: {msg}")
  | .ok (.none) => return false
  | .ok (.some (smt_term, ctx)) =>
    IO.FS.withTempDir (fun tempDir => do
      let filename := tempDir / s!"exprEvalTest.smt2"
      let ans ← Core.SMT.dischargeObligation
        { Options.default with verbose := .quiet }
        (LExpr.freeVars e) "z3" filename.toString
        [smt_term] ctx
      match ans with
      | .ok (.sat _,_) => return true
      | _ =>
        IO.println s!"Test failed on {e}"
        IO.println s!"The query: {repr smt_term}"
        throw (IO.userError "- failed"))

/--
If a randomly chosen value is <= odd / 10, pick from interesting vals,
otherwise fallback.
-/
private def pickInterestingValue {α} [Inhabited α]
    (odd: Nat) (interesting_vals:List α) (fallback:IO α): IO α
  := do
  if interesting_vals.isEmpty then
    fallback
  else
    let n := interesting_vals.length
    let k <- IO.rand 0 9
    if k <= odd then
      let idx <- IO.rand 0 (n - 1)
      return interesting_vals.getD idx Inhabited.default
    else
      fallback

private def pickRandInt (abs_bound:Nat): IO Int := do
  let rand_sign <- IO.rand 0 1
  let rand_size <- IO.rand 0 abs_bound
  return (if rand_sign = 0 then rand_size else - (Int.ofNat rand_size))

private def mkRandConst (ty:LMonoTy): IO (Option (LExpr CoreLParams.mono))
  := do
  match ty with
  | .tcons "int" [] =>
    let i <- pickInterestingValue 1 [0,1,-1] (pickRandInt 2147483648)
    return (.some (.intConst () i))
  | .tcons "bool" [] =>
    let rand_flag <- IO.rand 0 1
    let rand_flag := rand_flag == 0
    return (.some (.boolConst () rand_flag))
  | .tcons "real" [] =>
    let i <- pickInterestingValue 1 [0,1,-1] (pickRandInt 2147483648)
    let n <- IO.rand 1 2147483648
    return (.some (.realConst () (mkRat i n)))
  | .tcons "string" [] =>
    -- TODO: random string generator
    return (.some (.strConst () "a"))
  | .tcons "regex" [] =>
    -- TODO: random regex generator
    return (.some (.app ()
      (.op () (CoreIdent.unres "Str.ToRegEx") .none) (.strConst () ".*")))
  | .bitvec n =>
    let specialvals :=
      [0, 1, -1, Int.ofNat n, (Int.pow 2 (n-1)) - 1, -(Int.pow 2 (n-1))]
    let i <- pickInterestingValue 3 specialvals (IO.rand 0 ((Nat.pow 2 n) - 1))
    return (.some (.bitvecConst () n (BitVec.ofInt n i)))
  | _ =>
    return .none

def checkFactoryOps (verbose:Bool): IO Unit := do
  let arr:Array (LFunc CoreLParams) := Core.Factory
  let print (f:Format): IO Unit :=
    if verbose then IO.println f
    else return ()
  for e in arr do
    print f!"\nOp: {e.name} {e.inputs}"
    if ¬ e.typeArgs.isEmpty then
      print "- Has non-empty type arguments, skipping..."
      continue
    else
      let cnt := 50
      let mut unsupported := false
      let mut cnt_skipped := 0
      for _ in [0:cnt] do
        let args:List (Option (LExpr CoreLParams.mono))
          <- e.inputs.mapM (fun t => do
            let res <- mkRandConst t.snd
            match res with
            | .some x => return (.some x)
            | .none =>
              print s!"- Don't know how to create a constant for {t.snd}"
              return .none)
        if args.any (· == .none) then
          unsupported := true
          break
        else
          let args := List.map (Option.get!) args
          let expr := List.foldl (fun e arg => (.app () e arg))
            (LExpr.op () (CoreIdent.unres e.name.name) .none) args
          let res <- checkValid expr
          if ¬ res then
            if cnt_skipped = 0 then
              print f!"- did not evaluate to a constant; inputs: {args}"
              print "    (will omit printing other skipped cases)"
            cnt_skipped := cnt_skipped + 1
            continue
      if not unsupported then
        print s!"- Total {cnt} tests passed, {cnt_skipped} tests skipped"


open Lambda.LExpr.SyntaxMono
open Lambda.LExpr.Syntax
open Lambda.LTy.Syntax

/-- info: true -/
#guard_msgs in #eval (checkValid eb[#100])
/-- info: true -/
#guard_msgs in #eval (checkValid eb[#true])
/-- info: true -/
#guard_msgs in #eval (checkValid eb[#1 == #2])
/-- info: true -/
#guard_msgs in #eval (checkValid eb[if #1 == #2 then #false else #true])
/-- info: true -/
#guard_msgs in #eval (checkValid
  (.app () (.app () (.op () (CoreIdent.unres "Int.Add") .none) eb[#100]) eb[#50]))


-- This may take a while (~ 5min)
#eval (checkFactoryOps false)

open Plausible TestGen

deriving instance Arbitrary for Visibility

def test_lctx : LContext CoreLParams :=
{
  LContext.empty with
  functions := Core.Factory
  knownTypes := Core.KnownTypes
}

def test_ctx : TContext Visibility := ⟨[[]], []⟩

abbrev test_ty : LTy := .forAll [] <| .tcons "bool" []
#guard_msgs(drop all) in
#eval do
    let P : LExpr CoreLParams.mono → Prop := fun t => HasType test_lctx test_ctx t test_ty
    let t ← Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    IO.println s!"Generated {t}"
    let b ← checkValid t
    if ¬ b then
      IO.println s!"Invalid!"

end Tests

end Core
