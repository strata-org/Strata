/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import StrataTest.DL.Imperative.Arith
import Strata.DL.Imperative.EvalContext
import Strata.DL.SMT
import Init.Data.String.Extra

namespace Arith
---------------------------------------------------------------------

open Std (ToFormat Format format)
open Strata.SMT

def toSMTType (ty : Ty) : Except Format TermType := do
  match ty with
  | .Num => .ok .int
  | .Bool => .ok .bool

def toSMTTerm (E : Env) (e : Arith.Expr) : Except Format Term := do
  match e with
  | .Plus e1 e2 =>
    let e1 ← toSMTTerm E e1
    let e2 ← toSMTTerm E e2
    .ok (Term.app Op.add [e1, e2] .int)
  | .Mul e1 e2 =>
    let e1 ← toSMTTerm E e1
    let e2 ← toSMTTerm E e2
    .ok (Term.app Op.mul [e1, e2] .int)
  | .Eq e1 e2 =>
    let e1 ← toSMTTerm E e1
    let e2 ← toSMTTerm E e2
    .ok (Term.app Op.eq [e1, e2] .bool)
  | .Num n => .ok (Term.int n)
  | .Var v ty =>
    match ty with
    | none => .error f!"Variable {v} not type annotated; SMT encoding failed!"
    | some ty =>
      let ty ← toSMTType ty
      .ok (TermVar.mk false v ty)

def toSMTTerms (E : Env) (es : List Arith.Expr) : Except Format (List Term) := do
  match es with
  | [] => .ok []
  | e :: erest =>
    let et ← toSMTTerm E e
    let erestt ← toSMTTerms E erest
    .ok (et :: erestt)

def ProofObligation.toSMTTerms (E : Env) (d : Imperative.ProofObligation Arith.PureExpr) :
  Except Format (List Term) := do
  let assumptions := d.assumptions.flatten.map (fun a => a.snd)
  let assumptions_terms ← Arith.toSMTTerms E assumptions
  let obligation_pos_term ← Arith.toSMTTerm E d.obligation
  let obligation_term := Factory.not obligation_pos_term
  .ok (assumptions_terms ++ [obligation_term])

def encodeArithToSMTTerms (ts : List Term) : SolverM (List String × EncoderState) := do
  Solver.reset
  Solver.setLogic "ALL"
  let estate := EncoderState.init
  let (ids, estate) ← ts.mapM (Strata.SMT.Encoder.encodeTerm False) |>.run estate
  for id in ids do
    Solver.assert id
  let ids := (estate.terms.filter (fun t _ => t.isVar)).values
  return (ids, estate)

---------------------------------------------------------------------

  end Arith
