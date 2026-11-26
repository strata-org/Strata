/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.BetaReduceProps

/-! # Beta reduction keeps procedure bodies def-use well formed

A procedure body whose definitions apply lambdas: an alias redex `(fun y => y)(z)` and a
constant-lambda redex `(fun _ => 1)(w)`, whose argument reduction erases. Beta reduction
(`betaReduceProgram`) contracts both, reads no variable the input did not, and the reduced body
is def-use well formed for the predicates the input is. -/

namespace BetaReduceDefUseTest

open Core Lambda Imperative

/-- The identifier `n`. -/
def id' (n : String) : CoreIdent := ⟨n, ()⟩

/-- The integer variable `n`. -/
def iv (n : String) : Expression.Expr := .fvar Core.valueLoc (id' n) (some .int)

/-- The application of a lambda with body `b` to `a`. -/
def redex (b a : Expression.Expr) : Expression.Expr := .app Core.valueLoc (.abs Core.valueLoc "y" (some .int) b) a

/-- The body: `x := (fun y => y)(z)`, `v := (fun _ => 1)(w)`, `assert x == v`. -/
def body : Statements :=
  [.cmd (.cmd (.init (id' "x") (.forAll [] .int) (.det (redex (.bvar Core.valueLoc 0) (iv "z"))) #[])),
   .cmd (.cmd (.init (id' "v") (.forAll [] .int) (.det (redex (.intConst Core.valueLoc 1) (iv "w"))) #[])),
   .cmd (.cmd (.assert "a" (.eq Core.valueLoc (iv "x") (iv "v")) #[]))]

/-- A program with one procedure of body `body`. -/
def pgm : Program :=
  { decls := [.proc { header := { name := id' "P", typeArgs := [], inputs := [], outputs := [] },
                      spec := { preconditions := [], postconditions := [] },
                      body := .structured body false } #[]] }

/-- The structured body of the first procedure of `p`. -/
def firstBody (p : Program) : Statements :=
  match p.decls with
  | .proc q _ :: _ => match q.body with
    | .structured ss _ => ss
    | .cfg _ _ | .abstract => []
  | _ => []

/-- The entry names `z` and `w` are defined; no operator is declared. -/
def entry (n : CoreIdent) : Bool := n == id' "z" || n == id' "w"

#guard Block.defUseWellFormed entry (fun _ => false) body
#guard Block.defUseWellFormed entry (fun _ => false)
  (firstBody (BetaReduce.betaReduceProgram pgm))
#guard Block.getVars (firstBody (BetaReduce.betaReduceProgram pgm)) =
  [id' "z", id' "x", id' "v"]
#guard Block.getVars body = [id' "z", id' "w", id' "x", id' "v"]

end BetaReduceDefUseTest
