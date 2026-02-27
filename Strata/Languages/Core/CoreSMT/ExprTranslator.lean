/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.CoreSMT.IsCoreSMT

/-!
# Expression Translator for CoreSMT Verifier

Translates Core expressions to SMT terms by delegating to the existing
`Core.toSMTTerm` infrastructure in `SMTEncoder.lean`. Also provides type
translation via `LMonoTy.toSMTType`.
-/

namespace Strata.Core.CoreSMT

open Strata.SMT
open Lambda

/-- Translate a Core type to an SMT TermType using the existing encoder -/
def translateType (E : Core.Env) (ty : Core.Expression.Ty) (ctx : Core.SMT.Context) :
    Except Std.Format (TermType × Core.SMT.Context) :=
  Core.LMonoTy.toSMTType E ty.toMonoTypeUnsafe ctx

/-- Translate a Core expression to an SMT Term using the existing encoder -/
def translateExpr (E : Core.Env) (e : Core.Expression.Expr) (ctx : Core.SMT.Context) :
    Except Std.Format (Term × Core.SMT.Context) :=
  Core.toSMTTerm E [] e ctx

/-- Translate a list of Core expressions to SMT Terms -/
def translateExprs (E : Core.Env) (es : List Core.Expression.Expr) (ctx : Core.SMT.Context) :
    Except Std.Format (List Term × Core.SMT.Context) :=
  Core.toSMTTerms E es ctx

end Strata.Core.CoreSMT
