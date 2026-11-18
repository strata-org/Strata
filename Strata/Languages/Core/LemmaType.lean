/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.AxiomType

public section

namespace Core

open Lambda
open Std (ToFormat Format format)

namespace Lemma

/-- Type check a lemma against the type names in `scope`: its type parameters
    are distinct, and, with those that start with a reserved prefix renamed
    (`Lemma.renameReservedTypeArgs`), its proposition is a well-typed `bool`
    with them held rigid. Returns the renamed lemma with its checked
    proposition. The renaming and the rigid constants share one walk of the
    lemma's annotations. -/
def typeCheckIn (scope : Thunk (Std.HashSet String)) (C : Expression.TyContext)
    (Env : Expression.TyEnv) (l : Lemma) :
    Except Format (Lemma × Expression.TyEnv) := do
  checkTypeArgsNodup s!"Error in lemma {l.name}" l.typeArgs
  let annot := Thunk.mk fun _ => exprAnnotTys l.e
  let l' := l.renameReservedTypeArgs C Env fun _ => annot.get
  -- Built from `getTypeRefs` and `exprLitTyNames` so the annotation walk above is shared.
  let (e, Env') ← typeCheckProp scope "lemma" l.name l'.typeArgs C Env l'.e
    fun _ => annot.get.flatMap getTypeRefs ++ exprLitTyNames l.e
  .ok ({ l' with e }, Env')

end Lemma

end Core
