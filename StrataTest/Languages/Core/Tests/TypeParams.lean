/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

namespace Strata.TypeParamsTest

def typeParamsPrg : Program :=
#strata
program Core;

function left<T, U>(t: T, u: U) : T {
  t
}

function right<T, U>(t: T, u: U) : U {
  u
}

function double(a: int) : int {
  right(a, a) + left(a, a)
}

#end


end Strata.TypeParamsTest
