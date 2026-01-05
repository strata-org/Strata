/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.DDMTransform.Parse

-- Test polymorphic function declarations in DDM

def testPolymorphicFn :=
#strata
program Boogie;
function identity<a>(x : a) : a;
#end

#eval IO.println testPolymorphicFn

-- Test with multiple type parameters
def testMultiTypeParams :=
#strata
program Boogie;
function swap<a, b>(x : a, y : b) : b;
#end

#eval IO.println testMultiTypeParams
