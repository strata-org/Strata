/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/




import Strata.Languages.Boogie.Statement
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LExpr

namespace Boogie
---------------------------------------------------------------------

open Std (ToFormat Format format)
open Lambda

/-!
## Axioms

Axioms are propositions assumed to be true throughout a Strata.Boogie program.
They are passed on as assumptions to the SMT solver during VC generation. It's
the responsibility of the user to ensure that they are consistent.
-/

structure Axiom where
  name : BoogieLabel
  e : LExpr BoogieLParams.mono

instance : ToFormat (BoogieLParams.mono : LExprParamsT).base.Identifier :=
  show ToFormat BoogieIdent from inferInstance

instance : ToFormat Axiom where
  format a := f!"axiom {a.name}: {a.e};"

def Axiom.eraseTypes (a : Axiom) : Axiom :=
  { a with e := a.e.eraseTypes }

instance : ToFormat Axiom where
  format a := f!"axiom {a.name}: {a.e};"

---------------------------------------------------------------------
