/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprTypeEnv

namespace B3

open Std

/--
 Metadata for B3 identifiers.
 For now, we use a simple unit type since B3 doesn't have scoping.
-/
inductive B3IdentifierMetadata where
  | none
deriving DecidableEq, Repr

instance : ToFormat B3IdentifierMetadata where
  format
  | .none => ""

instance : ToString B3IdentifierMetadata where
  toString v := toString $ ToFormat.format v

abbrev B3Ident := Lambda.Identifier B3IdentifierMetadata
abbrev B3Label := String

def B3IdentDec : DecidableEq B3Ident := inferInstanceAs (DecidableEq (Lambda.Identifier B3IdentifierMetadata))

@[match_pattern]
def B3Ident.mk (s : String) : B3Ident := ⟨s, B3IdentifierMetadata.none⟩

instance : Coe String B3Ident where
  coe | s => .mk s

def B3Ident.toPretty (x : B3Ident) : String :=
  match x with | ⟨s, _⟩ => s

instance : ToFormat B3Ident where
  format i := B3Ident.toPretty i

instance : ToString B3Ident where
  toString | ⟨s, v⟩ => (toString $ ToFormat.format v) ++ (toString $ ToFormat.format s)

instance : Repr B3Ident where
  reprPrec | ⟨s, v⟩, _  => (ToFormat.format v) ++ (ToFormat.format s)

instance : Inhabited B3Ident where
  default := ⟨"_", .none⟩

instance : Lambda.HasGen B3IdentifierMetadata where
  genVar T := let (sym, state') := (Lambda.TState.genExprSym T.genState)
              (B3Ident.mk sym, { T with genState := state' })

namespace Syntax

open Lean Elab Meta Lambda.LExpr.SyntaxMono

scoped syntax ident : lidentmono

def elabB3Ident : Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := toString s.getId
    return ← mkAppM ``B3Ident.mk #[mkStrLit s]
  | _ => throwUnsupportedSyntax

instance : MkIdent B3IdentifierMetadata where
  elabIdent := elabB3Ident
  toExpr := .const ``B3IdentifierMetadata []

elab "b3[" e:lexprmono "]" : term => elabLExprMono (IDMeta:=B3IdentifierMetadata) e

end Syntax

end B3
