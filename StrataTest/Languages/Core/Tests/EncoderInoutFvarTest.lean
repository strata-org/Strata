/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
meta import Strata.Languages.Core.StatementEval

meta section

namespace Core

section Tests
open Statement Lambda Lambda.LTy.Syntax

/-! Regression: `mkReturnSubst` must type the fresh post-call variable of an
inout target even when the caller state has no binding for it.

The call-elimination path mints a fresh variable for each call LHS from the
type recovered in the caller state, defaulting to `none` on a lookup miss. For
an inout target whose post-call slot is not yet bound, that produced an untyped
free variable; a `free ensures` referencing it then reached the SMT encoder as
an unannotated free variable and failed to encode. The fix recovers the type
from the callee's declared output signature.

This drives `mkReturnSubst` directly with an inout target (`p : Ref`) absent
from the caller state, so the lookup misses. Without the fix the minted fvar's
type is `none`; with it the type is `Ref`. -/

private def refProc : Procedure :=
  { header := { name := "callee", typeArgs := [],
                inputs := [("p", mty[Ref])], outputs := [("p", mty[Ref])] },
    spec := { preconditions := [], postconditions := [] } }

-- The minted post-call fvar for inout `p` carries its declared type `Ref`
-- (not `none`), even though the caller state has no binding for `p`.
#guard
  let p : Expression.Ident := "p"
  let (_, lhs_post_subst, _) := mkReturnSubst refProc [p] Env.init
  let ty := lhs_post_subst.head?.bind (fun (_, e) =>
    match e with | .fvar _ _ ty => ty | _ => none)
  ty == some mty[Ref]

end Tests

end Core

end
