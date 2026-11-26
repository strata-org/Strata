/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.DL.Lambda.LExprWF
public import Strata.Util.Name
public import Strata.Languages.Core.NameMangling

/-! # Closing a lemma's type variables

`closeLemmaTypeVarsAvoiding`, the last step of `GenOpaqueTypeParams`. It lives in its own module,
which needs only the program syntax, so that code reasoning about the closed program need not
import the whole pass.
-/

public section

namespace Core
namespace GenOpaqueTypeParams

open Lambda Imperative

/-- Prefix of the opaque types that replace a type-checked lemma's remaining type
    variables.
    Kept as a literal copy in `Lambda.reservedNamePrefixes`, so type checking still
    rejects or renames program names that use it. -/
@[expose] def freeTyPrefix : String := "$__free_"

/-- One nullary opaque type declaration per pair `(tv, n)` of `names`, named
    `n`, and the substitution mapping each type variable `tv` to its opaque
    type. -/
def opaqueTypes (names : List (TyIdentifier × String)) : List Decl × Subst :=
  (names.map fun p => Decl.opaqueType p.2, Subst.ofNullaryConsts names)

/-- Replace every type variable that a lemma still has by a fresh
    opaque type, declared just before it, and drop the lemma's type parameters.
    The fresh names avoid the names in `taken`: the names the program declares
    with the free-type prefix (`Program.declaredNames`), and those generated before. Each `#`
    of the lemma's label is replaced in the names (`FreshPlainName.sanitize`), so a label
    containing `#` is renamed away, never rejected.
    This covers a type variable that is neither a type parameter of the lemma
    nor fixed by its formula, such as a type left open in a termination lemma
    built without a type check, which the SMT encoder would otherwise reject.
    It runs after `genOpaqueLemma`, which replaces the lemma's declared type
    parameters, and closes the type variables left in the formula's
    annotations.

    TODO: prove what this relies on: if the closed lemma holds, the original
    lemma holds at every instantiation of its type variables, since nothing
    constrains an opaque type. This is the argument by which
    `genOpaqueTypeParams` is model-preserving. -/
def closeLemmaTypeVarsAvoiding (taken : Std.HashSet String) (p : Program) :
    Program :=
  -- Two lemmas' sanitized bases may coincide (`a#b`, `a_b`), so `taken` grows with each name.
  let close (taken : Std.HashSet String) (l : Lemma) (md : MetaData Expression) :
      List Decl × Std.HashSet String :=
    match (annotTyVars l.e).eraseDups with
    | [] => ([.lemma l md], taken)
    | tvs =>
      let bases := tvs.mapIdx fun i _ => s!"{freeTyPrefix}{FreshPlainName.sanitize l.name}_{i}"
      let (names, taken) := Strata.Name.freshNames taken bases
      let (decls, S) := opaqueTypes (tvs.zip names)
      (decls ++ [.lemma { l with typeArgs := [], e := l.e.applyTypeSubst S } md], taken)
  let (decls, _) := p.decls.foldl (init := (#[], taken)) fun (acc, taken) d =>
    match d with
    | .lemma l md =>
      let (ds, taken) := close taken l md
      (acc ++ ds.toArray, taken)
    | d => (acc.push d, taken)
  { p with decls := decls.toList }

end GenOpaqueTypeParams
end Core

end -- public section
