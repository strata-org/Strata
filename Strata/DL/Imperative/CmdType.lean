/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.TypeContext

namespace Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

/--
Type checker for an Imperative Command.

The `TypeError` parameter for the `TypeContext` instance `TC` is a concrete type
here. We can change this to a more generic type in the future, if needed.
-/
def Cmd.typeCheck {P C T} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat (Cmd P)]
    [DecidableEq P.Ident] [TC : TypeContext P C T Format]
    (ctx: C) (τ : T) (c : Cmd P) : Except Format (Cmd P × T) := do

  try match c with

  | .init x xty e md =>
    match TC.lookup τ x with
    | none =>
      if x ∈ TC.freeVars e then
        .error f!"Variable {x} cannot appear in its own initialization expression!"
      else
        let (xty, τ) ← TC.preprocess ctx τ xty
        let (e, ety, τ) ← TC.inferType ctx τ c e
        let τ ← TC.unifyTypes τ [(xty, ety)]
        let (xty, τ) ← TC.postprocess ctx τ xty
        let τ := TC.update τ x xty
        let c := Cmd.init x xty e md
        .ok (c, τ)
    | some xty =>
      .error f!"Variable {x} of type {xty} already in context."

  | .set x e md =>
    match TC.lookup τ x with
    | none => .error f!"Cannot set undeclared variable {x}."
    | some xty =>
      let (e, ety, τ) ← TC.inferType ctx τ c e
      let τ ← TC.unifyTypes τ [(xty, ety)]
      let c := Cmd.set x e md
      .ok (c, τ)

  | .havoc x _md =>
    match TC.lookup τ x with
    | some _ => .ok (c, τ)
    | none => .error f!"Cannot havoc undeclared variable {x}."

  | .assert label e md =>
    let (e, ety, τ) ← TC.inferType ctx τ c e
    if TC.isBoolType ety then
       let c := Cmd.assert label e md
       .ok (c, τ)
    else
      .error f!"Assertion {label} expected to be of type boolean, \
                but inferred type is {ety}."

  | .assume label e md =>
    let (e, ety, τ) ← TC.inferType ctx τ c e
    if TC.isBoolType ety then
       let c := Cmd.assume label e md
       .ok (c, τ)
    else
      .error f!"Assumption {label} expected to be of type boolean, \
                but inferred type is {ety}."

  | .cover label e md =>
    let (e, ety, τ) ← TC.inferType ctx τ c e
    if TC.isBoolType ety then
       let c := Cmd.cover label e md
       .ok (c, τ)
    else
      .error f!"Cover {label} expected to be of type boolean, \
                but inferred type is {ety}."

  catch e =>
    -- Add source location to error messages.
    let sourceLoc := MetaData.formatFileRangeD c.getMetaData
    if sourceLoc.isEmpty then
      .error e
    else
      .error f!"{sourceLoc} {e}"

/--
Type checker for Imperative's Commands.
-/
def Cmds.typeCheck {P C T} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat (Cmd P)]
    [DecidableEq P.Ident] [TC : TypeContext P C T Format]
    (ctx: C) (τ : T) (cs : Cmds P) : Except Format (Cmds P × T) := do
  match cs with
  | [] => .ok ([], τ)
  | c :: crest =>
    let (c, τ) ← Cmd.typeCheck ctx τ c
    let (crest, τ) ← Cmds.typeCheck ctx τ crest
    .ok (c :: crest, τ)

---------------------------------------------------------------------
end Imperative
