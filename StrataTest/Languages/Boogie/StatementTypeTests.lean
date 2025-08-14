/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.StatementType

namespace Boogie
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)

open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.Syntax Boogie.Syntax

/--
info: ok: init (x : int) := (xinit : int)
x := (xinit : int)
init (y : int) := (xinit : int)
-/
#guard_msgs in
#eval do let ans ← typeCheck { TEnv.default with context := {types := [[("xinit", t[int])]] }}
                   Program.init
                   none
                   [.init "x" t[int] eb[xinit],
                    .set "x" eb[xinit],
                    .init "y" t[∀α. %α] eb[xinit]]
         return format ans.fst


/--
info: error: Type Checking [init (x : bool) := #true]: Variable x of type bool already in context.
-/
#guard_msgs in
#eval do let ans ← typeCheck { TEnv.default with
                                  context := { types := [[("x", t[bool])]] }}
                   Program.init
                   none
                   [
                    .init "x" t[bool] eb[#true]
                   ]
         return format ans

/--
info: ok: context:
types:   [(zinit, bool) (x, int) (y, int)]
aliases: []
state:
tyGen: 1
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst: ⏎
known types:
[∀[a, b]. (arrow a b), bool, int, string]
-/
#guard_msgs in
#eval do let ans ← typeCheck { TEnv.default with
                                  context := { types := [[("zinit", t[bool])]] }}
                    Program.init
                    none
                    [
                    .init "x" t[int] eb[#0],
                    .init "y" t[int] eb[#6],
                    .block "label_0" { ss :=

                      [Statement.init "z" t[bool] eb[zinit],
                       Statement.assume "z_false" eb[z == #false],

                      .ite eb[z == #false]
                        { ss := [Statement.set "x" eb[y]] }
                        { ss := [Statement.assert "trivial" eb[#true]]},

                      Statement.assert "x_eq_y_label_0" eb[x == y],
                      ]},
                    .assert "x_eq_y" eb[x == y]
                    ]
          return format ans.snd

/-- info: error: Cannot unify differently named type constructors bool and int! -/
#guard_msgs in
#eval do let ans ← typeCheck TEnv.default Program.init none
                    [
                    .init "x" t[int] eb[#0],
                    .init "y" t[int] eb[#6],
                    .init "z" t[bool] eb[if (x == y) then #true else #2]
                    ]
          return format ans

/--
info: error: Type Checking [init (x : int) := #1]: Variable x of type bool already in context.
-/
#guard_msgs in
#eval do let ans ← typeCheck TEnv.default Program.init none
                    [
                    .init "x" t[bool] eb[#true],
                    .block "label_0" {
                      ss := [
                        Statement.init "x" t[int] eb[#1]
                      ]
                    }
                    ]
          return format ans

/--
info: ok: context:
types:   [(x, int)]
aliases: []
state:
tyGen: 2
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst: ($__ty0, int)

known types:
[∀[a, b]. (arrow a b), bool, int, string]
-/
#guard_msgs in
#eval do let ans ← typeCheck TEnv.default Program.init none
                    [
                    .init "x" t[int] eb[#0],
                    .ite eb[x == #3]
                    { ss := [
                      Statement.init "y" t[∀α. %α] eb[x],
                      Statement.assert "local_y_eq_3" eb[y == #3]
                    ]}
                    {
                      ss := [
                        Statement.init "z" t[bool] eb[#true]
                      ]
                    }
                    ]
          return format ans.snd

/--
info: ok: init (x : int) := (#1 : int)
x := (#2 : int)
-/
#guard_msgs in
#eval do let ans ← typeCheck TEnv.default Program.init none
              [
              .init "x" t[∀a. %a] eb[#1],
              .set "x" eb[#2]
              ]
          return (format ans.fst)

/--
info: ok: context:
types:   [(fn, ∀[a]. (arrow a a)) (m1, (arrow int int)) (m2, (arrow (arrow bool int) int))]
aliases: []
state:
tyGen: 13
tyPrefix: $__ty
exprGen: 1
exprPrefix: $__var
subst: ($__ty10, int)
($__ty3, (arrow bool int))
($__ty5, (arrow bool int))
($__ty12, bool)
($__ty11, (arrow bool int))
($__ty7, bool)
($__ty6, bool)
($__ty9, bool)
($__ty8, (arrow bool bool))
($__ty2, int)
($__ty0, int)

known types:
[∀[a, b]. (arrow a b), bool, int, string]
-/
#guard_msgs in
#eval do let ans ← typeCheck { TEnv.default with
                                context := { types := [[("fn", t[∀a. %a → %a])]] }}
                      Program.init none
              [
              .init "m1" t[∀a. %a → int] eb[fn], -- var m : <a>[a]int
              .init "m2" t[∀a. %a → int] eb[(λ (%0 (fn #true)))],
              ]
          return (format ans.snd)

end Tests

---------------------------------------------------------------------

end Boogie
