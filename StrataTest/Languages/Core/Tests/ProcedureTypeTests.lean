/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.ProcedureType
import Strata.Languages.Core.Factory

meta section

namespace Core

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

/--
info: ok: (procedure P (x : int, out y : int)
 spec {
   requires [|0_lt_x|]: 0 < x;
   ensures [ret_y_lt_0]: y < 0;
   } {
   y := 0 - x;
 };
 ,
 context:
 types:   ⏎
 aliases: [] state: tyGen: 6 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: [])
-/
#guard_msgs in
#eval do let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init
                             { header := {name := "P",
                                          typeArgs := [],
                                          inputs := [("x", mty[int])],
                                          outputs := [("y", mty[int])] },
                               spec := { preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default, #[]⟩)],
                                         postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default, #[]⟩)] },
                               body := .structured [
                                 Statement.set "y" eb[((~Int.Sub #0) x)] .empty
                               ]
                             }
                            .empty
         return format ans


---------------------------------------------------------------------
-- Type-parameter well-formedness: `Procedure.typeCheck` rejects a signature type
-- variable not declared in `typeArgs` (mirroring `LFunc.type`'s check for
-- functions). This cannot be expressed in concrete `#strata` syntax — the
-- translator rejects the undeclared type before the checker runs (cf. the
-- AST-level Q2d test in `RigidTypeVarsTests`) — so it is exercised directly at
-- the `Procedure.typeCheck` level.
/--
info: error: [Undecl]: type variables [b] appear in the signature but are not declared in typeArgs [a]
-/
#guard_msgs in
#eval do let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init
                             { header := {name := "Undecl",
                                          typeArgs := ["a"],
                                          inputs := [("x", mty[%b])],
                                          outputs := [] },
                               spec := { preconditions := [], postconditions := [] },
                               body := .structured [] }
                            .empty
         return format ans

---------------------------------------------------------------------
-- Type-parameter well-formedness: `Procedure.typeCheck` rejects a type parameter
-- that uses the reserved generator-variable prefix `$__ty` (mirroring
-- `Function.typeCheck`'s guard). Instantiation renames each type parameter to a
-- fresh `$__ty<n>`; a user parameter literally named `$__ty0` would alias one of
-- these and the fresh→user back-renaming could capture. Not expressible in
-- concrete `#strata` syntax (the translator rejects `$`), so exercised at the
-- `Procedure.typeCheck` level.
/--
info: error: [GenPfx]: type parameters [$__ty0] use the reserved generator-variable prefix '$__ty'; rename them
-/
#guard_msgs in
#eval do let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init
                             { header := {name := "GenPfx",
                                          typeArgs := ["$__ty0"],
                                          inputs := [("x", Lambda.LMonoTy.ftvar "$__ty0")],
                                          outputs := [] },
                               spec := { preconditions := [], postconditions := [] },
                               body := .structured [] }
                            .empty
         return format ans

---------------------------------------------------------------------
-- Type-parameter well-formedness: `Procedure.typeCheck` rejects a procedure whose
-- pre/postconditions type-constrain a declared type parameter. Here `requires 0 < x`
-- (with `x : a`) unifies the fresh instantiation var `$__ty0` (standing for `a`) with
-- `int`, threading `$__ty0 ↦ int` into the persisted substitution. The rigid-refinement
-- guard (mirroring `Function.typeCheck`'s) then rejects: the body env's substitution no
-- longer fixes the rigid var `$__ty0`. Accepting this is a latent soundness gap (a caller
-- may instantiate `a := bool`, e.g. `call PreRefine(true)`, which the checker otherwise
-- accepts). Exercised at the `Procedure.typeCheck` level.
/--
info: error: [PreRefine]: rigid type variable '$__ty0' was refined to 'int'; a pre/postcondition or the signature over-constrains a declared type parameter
-/
#guard_msgs in
#eval do let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init
                             { header := {name := "PreRefine",
                                          typeArgs := ["a"],
                                          inputs := [("x", mty[%a])],
                                          outputs := [] },
                               spec := { preconditions := [("c", ⟨eb[((~Int.Lt #0) x)], .Default, #[]⟩)],
                                         postconditions := [] },
                               body := .structured [] }
                            .empty
         return format ans

---------------------------------------------------------------------
-- Old-prefix well-formedness: `Procedure.typeCheck` rejects a procedure whose body
-- DEFINES a variable whose name uses the reserved `old ` prefix (e.g. `var (old z) := 0`).
-- The `old ` prefix is reserved for the pre-state ghost bindings of in-out parameters
-- (`CoreIdent.mkOld`); a body-defined `old`-name would collide with that reserved namespace
-- and (in the soundness proof) makes the checker/spec body contexts disagree on an old key
-- that is not an inout ghost. The `init` freshness check does not catch it (a fresh `old z`
-- is unbound) and `checkModificationRights` only constrains *modified* vars, so a dedicated
-- guard is needed. Not expressible in concrete `#strata` syntax (identifiers cannot contain
-- the space in `old `), so exercised at the `Procedure.typeCheck` level.
/--
info: error: [CEX]: body modifies or defines variables [old z] whose names use the reserved 'old ' prefix; that prefix is reserved for pre-state inout parameter ghosts
-/
#guard_msgs in
#eval do let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init
                             { header := {name := "CEX",
                                          typeArgs := [],
                                          inputs := [],
                                          outputs := [] },
                               spec := { preconditions := [], postconditions := [] },
                               body := .structured [
                                 Statement.init (⟨"old z", ()⟩ : CoreIdent) t[int] (.det eb[#0]) .empty ] }
                            .empty
         return format ans

---------------------------------------------------------------------
-- Idempotency: type-checking preserves declared type parameters, so the output of a
-- polymorphic procedure re-type-checks. `Procedure.typeCheck` keeps `proc'.typeArgs`
-- while renaming the signature back to those names; clearing them to `[]` would leave
-- an internally inconsistent procedure (signature uses `a` but declares no type args)
-- that the `checkTypeArgsWF` guard rejects on the second pass.
/--
info: ok: (procedure Poly<a> (x : a, out y : a)
 {
   y := x;
 };
 ,
 context:
 types:   ⏎
 aliases: [] state: tyGen: 2 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: [(a, $__ty0) ($__ty1, $__ty0)])
-/
#guard_msgs in
#eval do let (proc', _) ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init
                             { header := {name := "Poly",
                                          typeArgs := ["a"],
                                          inputs := [("x", mty[%a])],
                                          outputs := [("y", mty[%a])] },
                               spec := { preconditions := [], postconditions := [] },
                               body := .structured [ Statement.set "y" eb[x] .empty ] }
                            .empty
         -- Re-type-check the output: must succeed (idempotency), preserving `typeArgs := [a]`.
         let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init proc' .empty
         return format ans

---------------------------------------------------------------------
end Tests
end Core

end
