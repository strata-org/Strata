/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! Reserved prefixes of generated names, and the check that a name uses none of them. -/

public section

namespace Lambda

/-- Prefix of the unification variables the type checker creates; declared type parameters
    may not use it. -/
@[expose, simp] def genTyPrefix : String := "$__ty"

/-- Prefix of the return-type parameters the eliminator generator declares. -/
@[expose] def elimTyPrefix : String := "$__elimty"

/-- Fixed prefix for generated type variable names. -/
def TState.tyPrefix : String := genTyPrefix

/-- Fixed prefix for generated expression variable names. -/
def TState.exprPrefix : String := "$__var"

/--
Prefix of argument names in generated datatype functions; disjoint from `TState.exprPrefix`.
-/
def exprPrefix : String := "$__tvar"

/-- Prefix of the nullary type constants the Core type checker uses for rigid type
    parameters. -/
@[expose] def skolemPrefix : String := "$__rigid_"

/-- Prefix of the type variables Core call elimination uses to instantiate a callee's
    contract. -/
@[expose] def callElimTyPrefix : String := "$__cety"

/-- Prefix of the type variables Core procedure inlining uses to instantiate a callee. -/
@[expose] def inlineTyPrefix : String := "$__inlinety"

/-- Name prefixes reserved for generated identifiers. The passes that use them choose names
    without checking all of the program's names, so a written name with one of these prefixes
    could be captured. -/
@[expose]
def reservedNamePrefixes : List String :=
  [genTyPrefix, skolemPrefix, elimTyPrefix, callElimTyPrefix, inlineTyPrefix]

/-- A name is allowed when it starts with no reserved prefix. -/
@[expose]
def isAllowedName (n : String) : Bool :=
  !(reservedNamePrefixes.any (fun p => n.startsWith p))

end Lambda

end -- public section
