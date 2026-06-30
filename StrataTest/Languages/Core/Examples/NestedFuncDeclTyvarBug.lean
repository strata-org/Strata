/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

open StrataDDM (Program)
---------------------------------------------------------------------
namespace Strata

/-! ## Nested funcDecl must respect rigidity of ambient procedure type variables

In `procedure proc<t>(...)`, the type parameter `t` is rigid: it may not be
refined to a concrete type inside the body. `Function.typeCheck` now enforces
this for nested function declarations (mirroring `CmdType.checkAnnotCompat` on
the var-initializer path).
-/

/-- A nested `function f() : int { y }` whose body `y : t` refines the rigid `t`
    to `int` is REJECTED. -/
def nestedFuncTyvarPgm : Program :=
#strata
program Core;

procedure proc<t>(y : t)
{
  function f() : int { y }
};

#end

/--
error: ❌ Type checking error.
Function 'f': rigid type variable 't' was refined to 'int' by the body
-/
#guard_msgs in
#eval Core.verify nestedFuncTyvarPgm

/-- Contrast: the var-initializer path rejects the same refinement of rigid `t`. -/
def varInitTyvarPgm : Program :=
#strata
program Core;

procedure proc<t>(y : t)
{
  var x : int := y;
};

#end

/--
error: ❌ Type checking error.
Rigid type variable 't' was refined to 'int' by the initializer
-/
#guard_msgs in
#eval Core.verify varInitTyvarPgm

/-- A nested function that does NOT refine the ambient `t` is still ACCEPTED:
    `g` is monomorphic and never touches `t`. Confirms the rigid check does not
    over-reject ordinary nested functions. -/
def okNestedFuncPgm : Program :=
#strata
program Core;

procedure proc<t>(y : t)
{
  function g(x : int) : int { x }
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval Core.verify okNestedFuncPgm

end Strata
---------------------------------------------------------------------
