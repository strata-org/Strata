/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.EvalContext

namespace Imperative
open Std (ToFormat Format format)

--------------------------------------------------------------------

/--
Partial evaluator for an Imperative Command.
-/
def Cmd.eval [EC : EvalContext P S] (σ : S) (c : Cmd P) : Cmd P × S :=
  match EC.lookupError σ with
  | some _ => (c, σ)
  | none =>
    match c with
    | .init x ty e md =>
      match EC.lookup σ x with
      | none =>
        let (e, σ) := EC.preprocess σ c e
        let e := EC.eval σ e
        let σ := EC.update σ x ty e
        let c' := .init x ty e md
        (c', σ)
      | some (xv, xty) => (c, EC.updateError σ (.InitVarExists (x, xty) xv))

    | .set x e md =>
      match EC.lookup σ x with
      | none => (c, EC.updateError σ (.AssignVarNotExists x e))
      | some (_xv, xty) =>
        let (e, σ) := EC.preprocess σ c e
        let e := EC.eval σ e
        let σ := EC.update σ x xty e
        let c' := .set x e md
        (c', σ)

    | .havoc x md =>
      match EC.lookup σ x with
      | none => (c, EC.updateError σ (.HavocVarNotExists x))
      | some (_, xty) =>
        let (e, σ) := EC.genFreeVar σ x xty
        let σ := EC.update σ x xty e
        let c' := .havoc x (md.pushElem (.var x) (.expr e))
        (c', σ)

    | .assert label e md =>
      let (e, σ) := EC.preprocess σ c e
      let e := EC.eval σ e
      let assumptions := EC.getPathConditions σ
      let c' := .assert label e md
      match EC.denoteBool e with
      | some true =>
        -- dbg_trace f!"{Format.line}Obligation {label} proved via evaluation!{Format.line}"
        -- (c', σ)
        (c', EC.deferObligation σ (ProofObligation.mk label assumptions e md))
      | some false =>
        if assumptions.isEmpty then
          (c', EC.updateError σ (.AssertFail label e))
        else
          (c', EC.deferObligation σ (ProofObligation.mk label assumptions e md))
      | none =>
        (c', EC.deferObligation σ (ProofObligation.mk label assumptions e md))

    | .assume label e md =>
      let (e, σ) := EC.preprocess σ c e
      let e := EC.eval σ e
      let c' := .assume label e md
      match EC.denoteBool e with
      | some true =>
        -- dbg_trace f!"[assume] {label} satisfied via evaluation.\n"
        (c', σ)
      | some false =>
        let σ := EC.addWarning σ (.AssumeFail label e)
        (c', EC.addPathCondition σ [(label, e)])
      | none =>
        (c', EC.addPathCondition σ [(label, e)])

/--
Partial evaluator for Imperative's Commands.
-/
def Cmds.eval [EvalContext P S] (σ : S) (cs : Cmds P) : Cmds P × S :=
  match cs with
  | [] => ([], σ)
  | c :: crest =>
    let (c, σ) := Cmd.eval σ c
    let (crest, σ) := Cmds.eval σ crest
    (c :: crest, σ)

---------------------------------------------------------------------

end Imperative
