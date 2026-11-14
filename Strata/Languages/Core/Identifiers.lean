/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.DL.Lambda.LExpr
public meta import Std.Do.Triple.SpecLemmas
public import Strata.DL.Lambda.LExpr
public import Strata.Util.FileRange

public section

/-- Source location of a Core expression: an optional file URI, a byte range in
that file, and related locations.

The URI is optional because some translators only know the byte range; it is
needed because inlining can move an expression into a different file's
procedure. -/
structure ExprSourceLoc where
  /-- The file this expression comes from, if known. -/
  uri : Option Strata.Uri := none
  /-- Byte range within the file. -/
  range : Strata.SourceRange
  /-- Other source locations behind this expression. When evaluation applies a
      lambda, the substituted copy lists the argument's and the lambda's
      locations here, so a report can cite both the use and the argument. -/
  relatedLocs : List (Option Strata.Uri × Strata.SourceRange) := []
deriving Repr, DecidableEq, Hashable

namespace ExprSourceLoc

/-- Location of an expression built by the tool rather than parsed from source.
`origin` names the part of the tool that built it (e.g. `"smt-model"`,
`"transform"`, `"test"`). There is deliberately no `none` location. -/
@[expose]
def synthesized (origin : String) : ExprSourceLoc :=
  { uri := some (.file s!"<synthesized:{origin}>"), range := Strata.SourceRange.none }

/-- The default location, used wherever a `default` metadata value is needed.
It is also the location of the values Core's semantic evaluator returns
(`Core.valueLoc`), so an expression built with default metadata and a value
built by the evaluator carry the same location. All `Inhabited` instances for
Core metadata must agree with this one. -/
instance : Inhabited ExprSourceLoc := ⟨synthesized "value"⟩

/-- Whether this location is a placeholder rather than parsed source: a
`synthesized` location, the `<unknown>` sentinel (`FileRange.unknown`), or an
empty file path with no byte range. An empty file path *with* a real range is a
parsed location (the prelude file is spelled this way), as is any URI-less
range-only location, so neither is synthesized. Reporting the placeholders as
synthesized is what keeps a placeholder location from being preferred over a
real parsed source range. -/
def isSynthesized (loc : ExprSourceLoc) : Bool :=
  match loc.uri with
  | some (.file p) => p.startsWith "<synthesized:" || p == "<unknown>" || (p == "" && loc.range.isNone)
  | none => false

/-- Location of expressions built by the `eb[...]` notation. -/
@[expose]
def elabDefault : ExprSourceLoc := synthesized "elab"

/-- A location with a byte range and no URI. -/
def ofRange (sr : Strata.SourceRange) : ExprSourceLoc := { range := sr }

/-- A location with a URI and a byte range. -/
def ofUriRange (uri : Strata.Uri) (sr : Strata.SourceRange) : ExprSourceLoc :=
  { uri := some uri, range := sr }

instance : Std.ToFormat ExprSourceLoc where
  format loc :=
    let fmt (u : Option Strata.Uri) (r : Strata.SourceRange) : Std.Format :=
      match u with
      | some u => f!"{u}:{r}"
      | none => f!"{r}"
    let primary := fmt loc.uri loc.range
    if loc.relatedLocs.isEmpty then primary
    else f!"{primary} (related: {loc.relatedLocs.map fun (u, r) => fmt u r})"

end ExprSourceLoc

end -- public section

namespace Core

public section

open Std

abbrev CoreIdent := Lambda.Identifier Unit

abbrev CoreExprMetadata := ExprSourceLoc
abbrev CoreLParams: Lambda.LExprParams := {Metadata := CoreExprMetadata, IDMeta := Unit}
abbrev CoreLabel := String

def CoreIdentDec : DecidableEq CoreIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Unit))

instance : Coe String CoreIdent where
  coe | s => ⟨s, ()⟩

def CoreIdent.toPretty (x : CoreIdent) : String := x.name

/-- String used to prefix identifiers representing pre-state inout parameters. -/
@[expose]
def CoreIdent.oldStr : String := "old "

/-- Create the `old name` identifier for an inout parameter named `name`. -/
@[expose]
def CoreIdent.mkOld (name : String) : CoreIdent := ⟨CoreIdent.oldStr ++ name, ()⟩

/-- `g ≠ CoreIdent.mkOld g.name` because `"old " ++ s` is strictly longer than `s`. -/
theorem CoreIdent.ne_mkOld (g : CoreIdent) : g ≠ CoreIdent.mkOld g.name := by
  intro h
  have h_name := congrArg Lambda.Identifier.name h
  simp only [mkOld, oldStr] at h_name
  have h1 : g.name.length < ("old " ++ g.name).length := by
    rw [String.length_append]
    have : (0 : Nat) < "old ".length := by decide
    omega
  rw [← h_name] at h1; omega

/-- `mkOld` is injective on the underlying name. -/
theorem CoreIdent.mkOld_injective {a b : String} (h : CoreIdent.mkOld a = CoreIdent.mkOld b) :
    a = b := by
  have h_name := congrArg Lambda.Identifier.name h
  simp only [mkOld, oldStr, String.append_right_inj] at h_name
  exact h_name

/-- Check whether an identifier is already an `old`-prefixed global name. -/
def CoreIdent.isOldIdent (ident : CoreIdent) : Bool :=
  CoreIdent.oldStr.toList.isPrefixOf ident.name.toList

instance : ToFormat CoreIdent where
  format i := CoreIdent.toPretty i

-- Explicit instances for CoreLParams field access
instance : ToFormat CoreLParams.Identifier :=
  show ToFormat CoreIdent from inferInstance

instance : DecidableEq CoreLParams.Identifier :=
  show DecidableEq CoreIdent from inferInstance

/-- Full representation of Strata Core Identifier with scope.
  This can be useful for both debugging and generating "unique" strings,
  for example, as labels of proof obligations in the VC generator.

  As a general guideline, whenever conversion from a `CoreIdent` to `String`
  is needed, _always use the `toString` method_." -/
instance : ToString CoreIdent where
  toString | ⟨s, ()⟩ => s

instance : Repr CoreIdent where
  reprPrec | ⟨s, ()⟩, _  => ToFormat.format s

instance : Inhabited CoreIdent where
  default := ⟨"_", ()⟩

/-- Reject repeated type parameters; the error message starts with `pfx`. -/
def checkTypeArgsNodup (pfx : String) (ta : List String) : Except Format Unit :=
  if !(decide ta.Nodup) then
    throw f!"{pfx}: duplicate type arguments {ta}"
  else
    pure ()

end -- public section

namespace Syntax

open Lean Elab Meta Lambda.LExpr.SyntaxMono

scoped syntax ident : lidentmono
/-- Elaborator for Core identifiers -/
meta def elabCoreIdent : Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := toString s.getId
    return mkApp3 (mkConst ``Lambda.Identifier.mk) (mkConst ``Unit) (mkStrLit s) (mkConst ``Unit.unit)
  | _ => throwUnsupportedSyntax

meta instance : MkLExprParams ⟨CoreExprMetadata, Unit⟩ where
  elabIdent := elabCoreIdent
  toExpr := mkApp2 (mkConst ``Lambda.LExprParams.mk) (mkConst ``CoreExprMetadata) (mkConst ``Unit)
  defaultMetadata := return mkConst ``ExprSourceLoc.elabDefault

elab "eb[" e:lexprmono "]" : term => elabLExprMono (T:=⟨CoreExprMetadata, Unit⟩) e

/--
info: Lambda.LExpr.op ExprSourceLoc.elabDefault { name := "old", metadata := () }
  none : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[~old]

/--
info: Lambda.LExpr.app ExprSourceLoc.elabDefault
  (Lambda.LExpr.op ExprSourceLoc.elabDefault { name := "old", metadata := () } none)
  (Lambda.LExpr.fvar ExprSourceLoc.elabDefault { name := "a", metadata := () }
    none) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[(~old a)]

open Lambda.LTy.Syntax in

/--
info: Lambda.LExpr.fvar ExprSourceLoc.elabDefault { name := "x", metadata := () }
  (some (Lambda.LMonoTy.tcons "bool" [])) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[(x : bool)]

end Syntax
