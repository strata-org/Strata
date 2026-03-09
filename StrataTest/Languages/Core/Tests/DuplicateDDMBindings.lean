/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- Duplicate DDM bindings (polymorphic functions, datatypes) are caught during
-- DDM elaboration and reported as errors (not panics).

/--
error: 'f1' already defined
-/
#guard_msgs in
def dupPolyFunctions : Program :=
#strata
program Core;
function f1<T1, T2>(x : T1) : Map T1 T2;
function f1<T1, T2>(x : T1) : Map T1 T2;
#end

---------------------------------------------------------------------

/--
error: Leaf already defined.
---
error: Node already defined.
-/
#guard_msgs in
def dupDatatypes : Program :=
#strata
program Core;
datatype Tree (a : Type) { Leaf(), Node(val: a, left: Tree a, right: Tree a) };
datatype Tree (a : Type) { Leaf(), Node(val: a, left: Tree a, right: Tree a) };
#end

---------------------------------------------------------------------
