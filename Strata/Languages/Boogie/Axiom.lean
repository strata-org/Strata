/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/




import Strata.Languages.Boogie.Statement

namespace Boogie

open Std (ToFormat Format format)
open Lambda

structure Axiom where
  name : BoogieLabel
  e : LExpr BoogieIdent

instance : ToFormat Axiom where
  format a := f!"axiom {a.name}: {a.e};"
