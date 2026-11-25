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

/-- Prefix of the type variables standing for a callee's type parameters that a call does not
    determine, in a precondition instantiated at that call. -/
@[expose] def precondTyVarPrefix : String := "$__precond_"

/-- Prefix of the type variables standing for a callee's type parameters that a call does not
    determine, when the callee is instantiated at that call. -/
@[expose] def callTyVarPrefix : String := "$__callty"

/-- Prefix of the nullary type constants the Core type checker uses for rigid type
    parameters. -/
@[expose] def skolemPrefix : String := "$__rigid_"

/-- Name prefixes reserved for generated type names. A program may declare a type whose name
    has one of these prefixes: type checking, `GenOpaqueTypeParams`, call elimination and
    procedure inlining avoid the program's type names, including those a body declares, for the
    types they generate (`$__free_`, `$__rigid_`, `$__opaque`, `$__cety`, `$__inlty`), and
    type checking renames a type parameter of a function, procedure or lemma that has a
    reserved prefix.

    The last five entries are copies of prefixes defined by the Core passes that generate
    them, which Lambda does not import: `Core.CallElim.callElimTyPrefix` (`$__cety`),
    `Core.ProcedureInlining.inlineTyPrefix` (`$__inlty`),
    `Core.TermCheck.termTyVarPrefix` (`$__termty`), `Core.abstractTyPrefix`
    (`$__abs_`) and `Core.GenOpaqueTypeParams.freeTyPrefix` (`$__free_`).

    Generated identifiers do not rely on this list: a Core pass records the prefixes of the
    `$__` names it generates in `Core.Program.usedIdentPrefixes`, and a pass that avoids the
    program's names skips collecting them when its prefix is free there. Type parameters still
    rely on it: the type checker and the proofs about generated type variables
    (`not_genTyPrefix_of_isAllowedName`) assume that no type parameter left after the renaming
    has one of these prefixes.

    TODO: rename type parameters against the recorded prefixes as well, so this list no longer
    needs copies of the passes' prefixes. -/
@[expose]
def reservedNamePrefixes : List String :=
  [genTyPrefix, skolemPrefix, elimTyPrefix, precondTyVarPrefix, callTyVarPrefix,
    "$__cety", "$__inlty", "$__termty", "$__abs_", "$__free_"]

/-- A name is allowed when it starts with no reserved prefix. -/
@[expose]
def isAllowedName (n : String) : Bool :=
  !(reservedNamePrefixes.any (fun p => n.startsWith p))

end Lambda

end -- public section
