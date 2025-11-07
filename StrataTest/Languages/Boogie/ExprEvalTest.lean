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

namespace Boogie

section Tests

open Lambda
open Std

def encode (e:LExpr LMonoTy Boogie.Visibility)
           (tenv:TEnv Visibility)
           (init_state:LState Boogie.Visibility):
    Except Format (Option (Strata.SMT.Term × SMT.Context))
  := do
  let init_state ← init_state.addFactory Boogie.Factory
  let lcont := { Lambda.LContext.default with
    functions := Boogie.Factory, knownTypes := Boogie.KnownTypes }
  let (e,_T) ← LExpr.annotate lcont tenv e
  let e_res := LExpr.eval init_state.config.fuel init_state e
  match e_res with
  | .const _ =>
    let env := Boogie.Env.init
    let (smt_term_lhs,ctx) ← Boogie.toSMTTerm env [] e SMT.Context.default
    let (smt_term_rhs,ctx) ← Boogie.toSMTTerm env [] e_res ctx
    let smt_term_eq := Strata.SMT.Factory.eq smt_term_lhs smt_term_rhs
    return (.some (smt_term_eq, ctx))
  | _ => return .none

def checkValid (e:LExpr LMonoTy Boogie.Visibility): IO Unit := do
  let tenv := TEnv.default
  let init_state := LState.init
  match encode e tenv init_state with
  | .error msg => throw (IO.userError s!"error: {msg}")
  | .ok (.none) => IO.println f!"- did not evaluate to a constant"
  | .ok (.some (smt_term, ctx)) =>
    let ans ← Boogie.dischargeObligation Options.default
      (LExpr.freeVars e) "z3" s!"exprEvalTest.smt2"
      [smt_term] ctx
    match ans with
    | .ok (.sat _,_) => IO.println f!"- passed!"
    | _ => throw (IO.userError "failed")

def mkRandConst (ty:LMonoTy): IO (Option (LExpr LMonoTy Boogie.Visibility))
  := do
  let rand_n <- IO.rand 0 100
  let rand_n2 <- IO.rand 0 100
  let rand_flag <- IO.rand 0 1
  let rand_flag := rand_flag == 0
  let rand_int:Int := if rand_flag then rand_n else Int.neg rand_n
  match ty with
  | .tcons "int" [] => return (.some (.intConst rand_int))
  | .tcons "bool" [] => return (.some (.boolConst rand_flag))
  | .tcons "real" [] => return (.some (.realConst (mkRat rand_int rand_n2)))
  | .tcons "string" [] => return (.some (.strConst "a"))
  | .tcons "regex" [] =>
    return (.some (.app
      (.op (BoogieIdent.unres "Str.ToRegEx") .none) (.strConst ".*")))
  | .bitvec n =>
    return (.some (.bitvecConst n (BitVec.ofNat n rand_n)))
  | _ => return .none

def checkFactoryOps: IO Unit := do
  let arr:Array (LFunc Boogie.Visibility) := Boogie.Factory
  for e in arr do
    IO.println f!"\nOp: {e.name} {e.inputs}"
    if ¬ e.typeArgs.isEmpty then
      IO.println "- Has non-empty type arguments, skipping..."
      continue
    else
      let args:List (Option (LExpr LMonoTy Visibility))
        <- e.inputs.mapM (fun t => do
          let res <- mkRandConst t.snd
          match res with
          | .some x => return (.some x)
          | .none =>
            IO.println s!"- Don't know how to create a constant for {t.snd}"
            return .none)
      if .none ∈ args then
        continue
      else
        let args := List.map (Option.get!) args
        IO.println s!"- Inputs: {args}"
        let expr := List.foldl (fun e arg => (.app e arg))
          (LExpr.op (BoogieIdent.unres e.name.name) .none) args
        checkValid expr


open Lambda.LExpr.SyntaxMono
open Lambda.LExpr.Syntax
open Lambda.LTy.Syntax

#eval (checkValid eb[#100])
#eval (checkValid eb[#true])
#eval (checkValid eb[#1 == #2])
#eval (checkValid eb[if #1 == #2 then #false else #true])
#eval (checkValid
  (.app (.app (.op (BoogieIdent.unres "Int.Add") .none) eb[#100]) eb[#50]))

#eval checkFactoryOps

end Tests

end Boogie
