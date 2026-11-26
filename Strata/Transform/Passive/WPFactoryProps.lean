/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.CoreProgram
public import Strata.Languages.Core.Factory
import Strata.Transform.RewritePassesProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Util.ExceptProps

/-! # Properties of the factory of the WP pipeline

The factory of the WP pipeline on a program (`Core.wpFactory`) keeps every function of
`Core.Factory` (`wpFactory_get`), so it resolves `Int.Add` and `Bool.Not` to Core's built-ins
(`wpFactory_intAdd`, `wpFactory_boolNot`), as every extension of `Core.Factory` resolves
`Bool.Not` (`addFactory_boolNot`).

Key theorems: `Core.WPLoop.wpFactory_get`, `Core.WPLoop.wpFactory_intAdd`,
`Core.WPLoop.wpFactory_boolNot`, `Core.WPLoop.addFactory_boolNot`. -/

namespace Core
namespace WPLoop

open Core.DefInline

public section

/-- The factory of the WP pipeline on a program keeps every function of `Core.Factory`: each of
    its extensions keeps the functions it extends. -/
theorem wpFactory_get {moreFns fac : Lambda.Factory CoreLParams} {p : Program} {n : String}
    {fn : Lambda.LFunc CoreLParams} (h : wpFactory moreFns p = .ok fac)
    (hn : (Core.Factory)[n]? = some fn) : fac[n]? = some fn := by
  obtain ⟨fac0, h0, h⟩ := (Except.bind_is_ok _ _ _).1 h
  replace hn := addFactory_get h0 hn
  clear h0
  generalize programDatatypes p = l at h
  induction l generalizing fac0 with
  | nil => exact Except.ok.inj h ▸ hn
  | cons b rest ih =>
    obtain ⟨F1, h1, h⟩ := (Except.bind_is_ok _ _ _).1 h
    obtain ⟨_, -, h1⟩ := (Except.bind_is_ok _ _ _).1 h1
    exact ih F1 (addFactory_get h1 hn) h

/-- The factory of the WP pipeline on a program resolves `Int.Add` to Core's built-in
    addition. -/
theorem wpFactory_intAdd {moreFns fac : Lambda.Factory CoreLParams} {p : Program}
    (h : wpFactory moreFns p = .ok fac) :
    fac["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func :=
  wpFactory_get h coreFactory_intAdd

/-- The factory of the WP pipeline on a program resolves `Bool.Not` to Core's built-in
    negation. -/
theorem wpFactory_boolNot {moreFns fac : Lambda.Factory CoreLParams} {p : Program}
    (h : wpFactory moreFns p = .ok fac) :
    fac["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func :=
  wpFactory_get h coreFactory_boolNot

/-- An extension of `Core.Factory` resolves `Bool.Not` to Core's built-in negation. -/
theorem addFactory_boolNot {moreFns fac : Lambda.Factory CoreLParams}
    (h : Core.Factory.addFactory moreFns = .ok fac) :
    fac["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func :=
  DefInline.addFactory_get h coreFactory_boolNot

end -- public section

end WPLoop
end Core
