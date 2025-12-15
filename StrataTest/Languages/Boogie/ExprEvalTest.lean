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
import Strata.Languages.Boogie.Env
import Strata.Languages.Boogie.Factory
import Strata.Languages.Boogie.Identifiers
import Strata.Languages.Boogie.Options
import Strata.Languages.Boogie.SMTEncoder
import Strata.Languages.Boogie.Verifier
import Strata.DL.Lambda.TestGen
import Strata.DL.Lambda.PlausibleHelpers
import Plausible.Gen

/-! This file does random testing of Boogie operations registered in factory, by
(1) choosing random constant inputs to the operations
(2) doing concrete evaluation and getting the results,
(3) SMT encoding the expression, and
(4) checking using the SMT solver whether the concrete output is equal to
the SMT expression.
-/

namespace Boogie

section Tests

open Lambda
open Std

def encode (e:LExpr BoogieLParams.mono)
           (tenv:TEnv Visibility)
           (init_state:LState BoogieLParams):
    Except Format (Option (Strata.SMT.Term × SMT.Context))
  := do
  let init_state ← init_state.addFactory Boogie.Factory
  let lcont := { Lambda.LContext.default with
    functions := Boogie.Factory, knownTypes := Boogie.KnownTypes }
  let (e,_T) ← LExpr.annotate lcont tenv e
  let e_res := LExpr.eval init_state.config.fuel init_state e
  match e_res with
  | .const _ _ =>
    let env := Boogie.Env.init
    let (smt_term_lhs,ctx) ← Boogie.toSMTTerm env [] e SMT.Context.default
    let (smt_term_rhs,ctx) ← Boogie.toSMTTerm env [] e_res ctx
    let smt_term_eq := Strata.SMT.Factory.eq smt_term_lhs smt_term_rhs
    return (.some (smt_term_eq, ctx))
  | _ => return .none

/--
Check whether concrete evaluation of e matches the SMT encoding of e.
Returns false if e did not reduce to a constant.
-/
def checkValid (e:LExpr BoogieLParams.mono): IO Bool := do
  let tenv := TEnv.default
  let init_state := LState.init
  match encode e tenv init_state with
  | .error msg => throw (IO.userError s!"error: {msg}")
  | .ok (.none) => return false
  | .ok (.some (smt_term, ctx)) =>
    let ans ← Boogie.dischargeObligation
      { Options.default with verbose := false }
      (LExpr.freeVars e) "z3" s!"exprEvalTest.smt2"
      [smt_term] ctx
    match ans with
    | .ok (.sat _,_) => return true
    | _ =>
      IO.println s!"Test failed on {e}"
      throw (IO.userError "- failed")

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

private def mkRandConst (ty:LMonoTy): IO (Option (LExpr BoogieLParams.mono))
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
      (.op () (BoogieIdent.unres "Str.ToRegEx") .none) (.strConst () ".*")))
  | .bitvec n =>
    let specialvals :=
      [0, 1, -1, Int.ofNat n, (Int.pow 2 (n-1)) - 1, -(Int.pow 2 (n-1))]
    let i <- pickInterestingValue 3 specialvals (IO.rand 0 ((Nat.pow 2 n) - 1))
    return (.some (.bitvecConst () n (BitVec.ofInt n i)))
  | _ =>
    return .none

def checkFactoryOps (verbose:Bool): IO Unit := do
  let arr:Array (LFunc BoogieLParams) := Boogie.Factory
  let print (f:Format): IO Unit :=
    if verbose then IO.println f
    else return ()
  for e in arr do
    print f!"\nOp: {e.name} {e.inputs}"
    if ¬ e.typeArgs.isEmpty then
      print "- Has non-empty type arguments, skipping..."
      continue
    else
      let cnt := 100
      let mut unsupported := false
      let mut cnt_skipped := 0
      for _ in [0:cnt] do
        let args:List (Option (LExpr BoogieLParams.mono))
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
            (LExpr.op () (BoogieIdent.unres e.name.name) .none) args
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
  (.app () (.app () (.op () (BoogieIdent.unres "Int.Add") .none) eb[#100]) eb[#50]))


-- This may take a while (~ 1min)
#eval (checkFactoryOps false)

open Plausible TestGen

deriving instance Arbitrary for Visibility

def test_lctx : LContext BoogieLParams :=
{
  LContext.empty with
  functions := Boogie.Factory
  knownTypes := Boogie.KnownTypes
}

def test_ctx : TContext Visibility := ⟨[[]], []⟩

abbrev test_ty : LTy := .forAll [] <| .tcons "bool" []

#guard_msgs(drop all) in
#eval do
    let P : LExpr BoogieLParams.mono → Prop := fun t => HasType test_lctx test_ctx t test_ty
    let t ← Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    IO.println s!"Generated {t}"
    let b ← checkValid t
    if ¬ b then
      IO.println s!"Invalid!"

end Tests

end Boogie
