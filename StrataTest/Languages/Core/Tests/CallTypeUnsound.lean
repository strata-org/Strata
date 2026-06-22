/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! ## Counterexample: call typechecker uses independent instantiations

The call typechecker in `Statement.typeCheckCmd` calls
`LMonoTySignature.instantiate` independently for inputs and outputs.
This means a polymorphic procedure whose type parameter appears in both
inputs AND outputs can be called with mismatched types — the input
instantiation and output instantiation are not forced to agree.

This test demonstrates that `Identity<T>(x : T, out y : T)` can be
"called" with `x : int` and `y : bool`, which should be a type error
(T cannot be both int and bool simultaneously), but the typechecker
accepts it.
-/

namespace Core

open Strata in
private def unsoundCallPgm :=
#strata
program Core;

procedure Identity<T>(x : T, out y : T)
{
  y := x;
};

procedure Bad(out result : bool)
{
  var n : int := 42;
  var b : bool := true;
  call Identity(n, out b);
  result := b;
};
#end

-- The typechecker correctly rejects this: T cannot be both int and bool.
/--
info: error: (1042-1066) Impossible to unify bool with $__ty2.
First mismatch: int with bool.
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram unsoundCallPgm)).fst
  Std.format (Core.typeCheck .default pgm.stripMetaData)

end Core

end
