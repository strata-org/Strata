/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.TypeContext

namespace Imperative
open Std (ToFormat Format format)
open Strata (DiagnosticModel FileRange)

public section

---------------------------------------------------------------------

/--
Type checker for an Imperative Command.

The `TypeError` parameter for the `TypeContext` instance `TC` is `DiagnosticModel`.
-/
def Cmd.typeCheck {P C T} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat (Cmd P)]
    [DecidableEq P.Ident] [TC : TypeContext P C T DiagnosticModel]
    (ctx: C) (τ : T) (c : Cmd P) : Except DiagnosticModel (Cmd P × T) := do

  try match c with

  | .init x xty e md =>
    match TC.lookup τ x with
    | none =>
      match e with
      | .det expr =>
        if x ∈ TC.freeVars expr then
          .error <| md.toDiagnosticF f!"Variable {x} cannot appear in its own initialization expression!"
        else
          let (xty, τ) ← TC.preprocess ctx τ xty
          let (expr, ety, τ) ← TC.inferType ctx τ c expr
          let τ ← TC.unifyTypes τ [(xty, ety)]
          let (xty, τ) ← TC.postprocess ctx τ xty
          let τ := TC.update τ x xty
          let c := Cmd.init x xty (.det expr) md
          .ok (c, τ)
      | .nondet =>
        let (xty, τ) ← TC.preprocess ctx τ xty
        let (xty, τ) ← TC.postprocess ctx τ xty
        let τ := TC.update τ x xty
        let c := Cmd.init x xty .nondet md
        .ok (c, τ)
    | some xty =>
      .error <| md.toDiagnosticF f!"Variable {x} of type {xty} already in context."

  | .set x e md =>
    match TC.lookup τ x with
    | none => .error <| md.toDiagnosticF f!"Cannot set undeclared variable {x}."
    | some xty =>
      match e with
      | .det expr =>
        let (expr, ety, τ) ← TC.inferType ctx τ c expr
        let τ ← TC.unifyTypes τ [(xty, ety)]
        let c := Cmd.set x (.det expr) md
        .ok (c, τ)
      | .nondet =>
        .ok (c, τ)

  | .assert label e md =>
    let (e, ety, τ) ← TC.inferType ctx τ c e
    if TC.isBoolType ety then
       let c := Cmd.assert label e md
       .ok (c, τ)
    else
      .error <| md.toDiagnosticF f!"Assertion {label} expected to be of type boolean, \
                but inferred type is {ety}."

  | .assume label e md =>
    let (e, ety, τ) ← TC.inferType ctx τ c e
    if TC.isBoolType ety then
       let c := Cmd.assume label e md
       .ok (c, τ)
    else
      .error <| md.toDiagnosticF f!"Assumption {label} expected to be of type boolean, \
                but inferred type is {ety}."

  | .cover label e md =>
    let (e, ety, τ) ← TC.inferType ctx τ c e
    if TC.isBoolType ety then
       let c := Cmd.cover label e md
       .ok (c, τ)
    else
      .error <| md.toDiagnosticF f!"Cover {label} expected to be of type boolean, \
                but inferred type is {ety}."

  catch e =>
    -- Add source location to error messages if not already present.
    .error <| e.withRangeIfUnknown (getFileRange c.getMetaData |>.getD FileRange.unknown)

/--
Type checker for Imperative's Commands.
-/
def Cmds.typeCheck {P C T} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat (Cmd P)]
    [DecidableEq P.Ident] [TC : TypeContext P C T DiagnosticModel]
    (ctx: C) (τ : T) (cs : Cmds P) : Except DiagnosticModel (Cmds P × T) := do
  match cs with
  | [] => .ok ([], τ)
  | c :: crest =>
    let (c, τ) ← Cmd.typeCheck ctx τ c
    let (crest, τ) ← Cmds.typeCheck ctx τ crest
    .ok (c :: crest, τ)

---------------------------------------------------------------------
end -- public section
end Imperative
