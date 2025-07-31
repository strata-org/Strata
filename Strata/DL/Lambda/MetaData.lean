/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

namespace Lambda
/--
Metadata annotations.

[Stopgap] We will eventually design a structured metadata language that we will
modify along with our code transformation functions.
-/
structure Info where
  value : String
  deriving DecidableEq, Repr

end Lambda
