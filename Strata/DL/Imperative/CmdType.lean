/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.TypeContext

namespace Imperative
open Std (ToFormat Format format)
open MetaData (formatFileRangeD MetaDataElem)

---------------------------------------------------------------------

/--
Type checker for an Imperative Command.
-/
def Cmd.typeCheck [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat (Cmd P)]
    [DecidableEq P.Ident] [TC : TypeContext P C T (MetaData P)]
    (ctx: C) (τ : T) (c : Cmd P) : Except Format (Cmd P × T) := do

  let mdfun := fun (md : MetaData P) => f!"({formatFileRangeD md}) "
  match c with

  | .init x xty e md =>
    match TC.lookup τ x with
    | none =>
      if x ∈ TC.freeVars e then
        .error f!"{Format.line}{mdfun md}Type Checking [{c}]: \
                  Variable {x} cannot appear in its own initialization expression!"
      else
        let xty_md := (md.pushElem MetaData.lValue (.msg s!"{format x}"))
        let (xty, τ) ← TC.preprocess ctx τ xty xty_md
        let ety_md := (md.pushElem MetaData.rValueOf (.msg s!"{format x}"))
        let (e, ety, τ) ← TC.inferType ctx τ c e ety_md
        let τ ← TC.unifyTypes τ [((xty, ety), some (xty_md, ety_md))] md
        let (xty, τ) ← TC.postprocess ctx τ xty md
        let τ := TC.update τ x xty
        let c := Cmd.init x xty e md
        .ok (c, τ)
    | some xty =>
      .error f!"{Format.line}{mdfun md}Type Checking [{c}]: \
                Variable {x} of type {xty} already in context."

  | .set x e md =>
    match TC.lookup τ x with
    | none => .error f!"{Format.line}{mdfun md}Type Checking [{c}]: \
                        Cannot set undefined variable {x}."
    | some xty =>
      let (e, ety, τ) ← TC.inferType ctx τ c e md
      let xty_md := (md.pushElem MetaData.lValue (.msg s!"{format x}"))
      let ety_md := (md.pushElem MetaData.rValueOf (.msg s!"{format x}"))
      let τ ← TC.unifyTypes τ [((xty, ety), some (xty_md, ety_md))] md
      let c := Cmd.set x e md
      .ok (c, τ)

  | .havoc x md =>
    match TC.lookup τ x with
    | some _ => .ok (c, τ)
    | none => .error f!"{Format.line}{mdfun md}Type Checking [{c}]: \
                        Cannot havoc undefined variable {x}."

  | .assert label e md =>
    let (e, ety, τ) ← TC.inferType ctx τ c e md
    if TC.isBoolType ety then
       let c := Cmd.assert label e md
       .ok (c, τ)
    else
      .error f!"{Format.line}{mdfun md}Type Checking [assert {label}]: \
                Assertion expected to be of type boolean, but inferred type is {ety}."

  | .assume label e md =>
    let (e, ety, τ) ← TC.inferType ctx τ c e md
    if TC.isBoolType ety then
       let c := Cmd.assume label e md
       .ok (c, τ)
    else
      .error f!"{Format.line}{mdfun md}Type Checking [assume {label}]: \
                Assumption expected to be of type boolean, but inferred type is {ety}."

/--
Type checker for Imperative's Commands.
-/
def Cmds.typeCheck {P C T} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat (Cmd P)]
    [ToFormat (MetaDataElem { Expr := P.Expr, Identifier := P.Ident})]
    [DecidableEq P.Ident] [TC : TypeContext P C T (MetaData P)]
    (ctx: C) (τ : T) (cs : Cmds P) : Except Format (Cmds P × T) := do
  match cs with
  | [] => .ok ([], τ)
  | c :: crest =>
    let (c, τ) ← Cmd.typeCheck ctx τ c
    let (crest, τ) ← Cmds.typeCheck ctx τ crest
    .ok (c :: crest, τ)

---------------------------------------------------------------------
end Imperative
