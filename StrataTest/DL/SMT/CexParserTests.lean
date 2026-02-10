/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.CexParser

/-! ## Tests for CexParser -/

namespace Strata.SMT.CExParser
open Std (Format ToFormat format)

/-- info: -/
#guard_msgs in
#eval format $ parseCEx ""

/-- info: (t1 -8) (t4 0) (t0 0) -/
#guard_msgs in
#eval format $ parseCEx "((t1 -8) (t4 0) (t0 0))"

/-- info: (t1 true) (t4 (+ blah blah)) (t0 (test x (foo y)) -/
#guard_msgs in
#eval format $ parseCEx "((t1 true)    (t4 (+ blah blah))
(t0 (test x (foo y))))"

/-- info: (t1 (- 8)) (t4 0) (t0 0) -/
#guard_msgs in
#eval format $ parseCEx "((t1 (- 8)) (t4 0) (t0 0))"

end Strata.SMT.CExParser
