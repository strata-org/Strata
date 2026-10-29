/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import StrataLaurel.Implementation.LaurelAST
import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator

namespace Strata.Laurel

open Std (Format ToFormat)
public section

/--
A single declaration in a CoreWithLaurelTypes program. Declarations are in
dependency order (dependencies before dependents).
-/
inductive OrderedDecl where
  /-- A group of functions (single non-recursive, or mutually recursive).
      Invariant: `funcs.length > 1 → isRecursive = true`. -/
  | funcs (funcs : List Procedure) (isRecursive : Bool)
  /-- A single (non-functional) procedure. -/
  | procedure (procedure : Procedure)
  /-- A group of (possibly mutually recursive) datatypes. -/
  | datatypes (dts : List DatatypeDefinition)
  /-- An opaque (natively implemented) type. Always emitted before everything else: it has
      no constructor arguments, so it can neither depend on another declaration nor take
      part in a cycle, while a datatype's field types may well refer to it. -/
  | opaqueType (ot : OpaqueTypeDefinition)
  /-- A named constant. -/
  | constant (c : Constant)

/--
A program whose declarations have been grouped and topologically ordered,
using Laurel types. Produced by `orderFunctionsAndProcedures` from a
`LaurelProgram`.
-/
structure CoreWithLaurelTypes where
  decls : List OrderedDecl

/-- Format a procedure as a function, replacing the leading "procedure" keyword with "function". -/
private def formatAsFunction (proc : Procedure) : Format :=
  let s := (ToFormat.format proc).pretty 100
  let s := if s.startsWith "procedure" then "function" ++ s.drop "procedure".length else s
  Format.text s

def formatOrderedDecl : OrderedDecl → Format
  | .funcs funcs _ => Format.joinSep (funcs.map formatAsFunction) "\n\n"
  | .procedure proc => ToFormat.format proc
  | .datatypes dts => Format.joinSep (dts.map ToFormat.format) "\n\n"
  | .opaqueType ot => ToFormat.format ot
  | .constant c => ToFormat.format c

instance : ToFormat OrderedDecl where
  format := formatOrderedDecl

def formatCoreWithLaurelTypes (p : CoreWithLaurelTypes) : Format :=
  Format.joinSep (p.decls.map formatOrderedDecl) "\n\n"

instance : ToFormat CoreWithLaurelTypes where
  format := formatCoreWithLaurelTypes

end -- public section
