/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.DDMTransform.Translate.Basic

/-!
DDM type expressions → `LMonoTy`. Used pervasively by the rest of
the translator for procedure bindings, function signatures, and
match scrutinee types.
-/

namespace Strata.CoreMatch.Translate

open Strata
open Lambda
open Strata.CoreMatchDDM

public section

private def typeRange : CoreMatchType SourceRange → SourceRange
  | .bvar m _    | .tvar m _   | .fvar m _ _
  | .arrow m _ _
  | .bool m      | .int m      | .string m   | .regex m  | .real m
  | .bv1 m       | .bv8 m      | .bv16 m     | .bv32 m   | .bv64 m
  | .Map m _ _   | .Sequence m _ => m

private def getTypeBVar (m : SourceRange) (i : Nat) : TransM LMonoTy := do
  let xs := (← StateT.get).tyBVars
  match xs[xs.size - 1 - i]? with
  | some n => return .ftvar n
  | none   => throwAt m s!"unknown type bvar {i}"

def getFVarName (m : SourceRange) (i : Nat) : TransM String := do
  match (← StateT.get).gctx.nameOf? i with
  | some n => return n
  | none   => throwAt m s!"unknown free variable {i}"

partial def toCoreMonoType : CoreMatchType SourceRange → TransM LMonoTy
  | .int _      => return .int
  | .bool _     => return .bool
  | .string _   => return .string
  | .real _     => return .real
  | .bv1 _      => return .bitvec 1
  | .bv8 _      => return .bitvec 8
  | .bv16 _     => return .bitvec 16
  | .bv32 _     => return .bitvec 32
  | .bv64 _     => return .bitvec 64
  | .arrow _ a b   => return .arrow (← toCoreMonoType a) (← toCoreMonoType b)
  | .Map _ k v     => return .tcons "Map" [← toCoreMonoType k, ← toCoreMonoType v]
  | .Sequence _ a  => return .tcons "Sequence" [← toCoreMonoType a]
  | .tvar _ n      => return .ftvar n
  | .fvar m i args => return .tcons (← getFVarName m i) (← args.toList.mapM toCoreMonoType)
  | .bvar m i      => getTypeBVar m i
  | t => throwAt (typeRange t) s!"unsupported type: {repr t}"

/-- Strip a scrutinee's monomorphic type to a datatype name; fail
with a diagnostic if it isn't a `tcons`. -/
def expectDatatype (range : SourceRange) (mty : LMonoTy) : TransM String :=
  match mty with
  | .tcons n _ => return n
  | _ => throwAt range s!"match scrutinee must be a datatype, got: {repr mty}"

end

end Strata.CoreMatch.Translate
