/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.EvalContext

namespace Imperative
open Std (ToFormat Format format)

public section

--------------------------------------------------------------------

/--
Symbolic simulation for an Imperative Command.
-/
def Cmd.eval [BEq P.Ident] [EC : EvalContext P S] (σ : S) (c : Cmd P) : Cmd P × S :=
  match EC.lookupError σ with
  | some _ => (c, σ)
  | none =>
    match c with
    | .init x ty e md =>
      match EC.lookup σ x with
      | none =>
        match e with
        | .det expr =>
          let (expr, σ) := EC.preprocess σ c expr
          let expr := EC.eval σ expr
          let σ := EC.update σ x ty expr
          let c' := .init x ty (.det expr) md
          (c', σ)
        | .nondet =>
          -- Unconstrained initialization - generate a fresh value
          let (expr, σ) := EC.genFreeVar σ x ty
          let σ := EC.update σ x ty expr
          let c' := .init x ty .nondet md
          (c', σ)
      | some (xv, xty) => (c, EC.updateError σ (.InitVarExists (x, xty) xv))

    | .set x e md =>
      match EC.lookup σ x with
      | none =>
        match e with
        | .det expr => (c, EC.updateError σ (.AssignVarNotExists x expr))
        | .nondet => (c, EC.updateError σ (.HavocVarNotExists x))
      | some (_xv, xty) =>
        match e with
        | .det expr =>
          let (expr, σ) := EC.preprocess σ c expr
          let expr := EC.eval σ expr
          let σ := EC.update σ x xty expr
          let c' := .set x (.det expr) md
          (c', σ)
        | .nondet =>
          let (expr, σ) := EC.genFreeVar σ x xty
          let σ := EC.update σ x xty expr
          let c' := .set x .nondet (md.pushElem (.var x) (.expr expr))
          (c', σ)

    | .assert label e md =>
      let (e, σ) := EC.preprocess σ c e
      let e := EC.eval σ e
      let assumptions := EC.getPathConditions σ
      let c' := .assert label e md
      let propType := match md.getPropertyType with
        | some s => if s == MetaData.divisionByZero then .divisionByZero
                    else if s == MetaData.arithmeticOverflow then .arithmeticOverflow
                    else .assert
        | none => .assert
      match EC.denoteBool e with
      | some true => -- Proved via evaluation.
        (c', EC.deferObligation σ (ProofObligation.mk label propType assumptions e md))
      | some false =>
        if assumptions.isEmpty then
          (c', EC.updateError σ (.AssertFail label e))
        else
          (c', EC.deferObligation σ (ProofObligation.mk label propType assumptions e md))
      | none =>
        (c', EC.deferObligation σ (ProofObligation.mk label propType assumptions e md))

    | .assume label e md =>
      let (e, σ) := EC.preprocess σ c e
      let e := EC.eval σ e
      let c' := .assume label e md
      match EC.denoteBool e with
      | some true => -- Satisified via evaluation.
        (c', σ)
      | some false =>
        let σ := EC.addWarning σ (.AssumeFail label e)
        (c', EC.addPathCondition σ [(label, e)])
      | none =>
        (c', EC.addPathCondition σ [(label, e)])

    | .cover label e md =>
      let (e, σ) := EC.preprocess σ c e
      let e := EC.eval σ e
      let assumptions := EC.getPathConditions σ
      let c' := .cover label e md
      (c', EC.deferObligation σ (ProofObligation.mk label .cover assumptions e md))

/--
Symbolic simulation for Imperative's Commands.
-/
def Cmds.eval [BEq P.Ident] [EvalContext P S] (σ : S) (cs : Cmds P) : Cmds P × S :=
  match cs with
  | [] => ([], σ)
  | c :: crest =>
    let (c, σ) := Cmd.eval σ c
    let (crest, σ) := Cmds.eval σ crest
    (c :: crest, σ)

--------------------------------------------------------------------

def stuck {P S} [EC : EvalContext P S] (σ : S) (message : String) : S :=
  EC.updateError σ (.Misc message)

/--
Concrete execution for an Imperative Command.

This currently has substantial overlap with `eval`,
but it is likely to diverge further in the future,
especially when we add an oracle to make choices for non-deterministic elements.
-/
def Cmd.run {P S} [BEq P.Ident] [EC : EvalContext P S] (σ : S) (c : Cmd P) : S :=
  match EC.lookupError σ with
  | some _ => σ
  | none =>
    match c with
    | .init x ty e _ =>
      match EC.lookup σ x with
      | none =>
        match e with
        | .det expr =>
          let (expr, σ) := EC.preprocess σ c expr
          let expr := EC.eval σ expr
          EC.update σ x ty expr
        | .nondet =>
          -- Unconstrained initialization - generate a fresh value
          -- Reading the value of this variable will cause execution to get stuck,
          -- but this still allows the common pattern of initializing a variable
          -- and then immediately overwriting it with a deterministic value.
          let (expr, σ) := EC.genFreeVar σ x ty
          EC.update σ x ty expr
      | some (xv, xty) => EC.updateError σ (.InitVarExists (x, xty) xv)

    | .set x e _ =>
      match EC.lookup σ x with
      | none =>
        match e with
        | .det expr => EC.updateError σ (.AssignVarNotExists x expr)
        | .nondet => EC.updateError σ (.HavocVarNotExists x)
      | some (_xv, xty) =>
        match e with
        | .det expr =>
          let (expr, σ) := EC.preprocess σ c expr
          let expr := EC.eval σ expr
          EC.update σ x xty expr
        | .nondet =>
          -- See .init comment above
          let (expr, σ) := EC.genFreeVar σ x xty
          EC.update σ x xty expr

    | .assert label e _ =>
      let (e, σ) := EC.preprocess σ c e
      let e := EC.eval σ e
      match EC.denoteBool e with
      | some true =>
        σ
      | some false =>
        EC.updateError σ (.AssertFail label e)
      | none =>
        EC.updateError σ (.Misc f!"assert ({label}) condition did not reduce to bool")

    | .assume label e _ =>
      let (e, σ) := EC.preprocess σ c e
      let e := EC.eval σ e
      match EC.denoteBool e with
      | some true =>
        σ
      | some false =>
        EC.updateError σ (.Misc f!"assume ({label}) condition is false")
      | none =>
        EC.updateError σ (.Misc f!"assume ({label}) condition did not reduce to bool")

    | .cover _ _ _ =>
      -- In the future we can record when a cover is true
      -- and assert it was hit at least once later on
      EC.updateError σ (.Misc s!"cover is not yet supported")

/--
Concrete execution for Imperative's Commands.
-/
def Cmds.run [BEq P.Ident] [EvalContext P S] (σ : S) (cs : Cmds P) : S :=
  match cs with
  | [] => σ
  | c :: crest =>
    let σ := Cmd.run σ c
    Cmds.run σ crest

---------------------------------------------------------------------

end -- public section
end Imperative
