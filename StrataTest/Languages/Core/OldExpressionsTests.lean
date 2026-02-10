/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.OldExpressions

/-! ## Tests for OldExpressions -/

namespace Core.OldExpressions
open Lambda.LExpr.SyntaxMono Lambda.LTy.Syntax Core.Syntax

/-- info: true -/
#guard_msgs in
#eval normalizeOldExpr eb[(~old (f g))] == eb[((~old f) (~old g))]

/-- info: true -/
#guard_msgs in
#eval normalizeOldExpr eb[((~old (~old f)) g)] == eb[((~old f) g)]

/-- info: true -/
#guard_msgs in
#eval normalizeOldExpr eb[(~old #2)] == eb[#2]

/-- info: true -/
#guard_msgs in
#eval normalizeOldExpr eb[(~old ((f a) g))] == eb[(((~old f) (~old a)) (~old g))]

/-- info: true -/
#guard_msgs in
#eval containsOldExpr eb[(~old (f g))]

/-- info: false -/
#guard_msgs in
#eval containsOldExpr eb[(f x)]

/-- info: [u:f, u:g] -/
#guard_msgs in
#eval extractOldExprVars eb[((~old f) (~old g))]

end Core.OldExpressions
