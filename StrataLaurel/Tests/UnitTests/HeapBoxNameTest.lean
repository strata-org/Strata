/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Implementation.HeapParameterization

/-
Validates the names that `HeapParameterization` generates

N.B. These could be upgraded to theorems once Lean has better theorem coverage for the
`String` operations that implement the predicates.
-/


meta section

open Strata.Laurel

/-! A box constructor reads as neither a selector nor a tester. -/
#guard !Lambda.isSelectorName (boxCtorName "testComposite").text
#guard !Lambda.isTesterName (boxCtorName "testComposite").text

/-! The box destructor is a genuine selector on `$Box`, and still reads as one. -/
#guard Lambda.isSelectorName (boxDestructorForTag "testComposite").text
#guard !Lambda.isTesterName (boxDestructorForTag "testComposite").text

end
