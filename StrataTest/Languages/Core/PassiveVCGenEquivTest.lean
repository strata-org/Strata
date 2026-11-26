/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.PassiveVCGen
meta import Strata.DL.SMT.Term
meta import Strata.DL.SMT.Encoder
meta import Strata.Languages.Core.Env
meta import Strata.Languages.Core.Expressions
meta import Strata.Languages.Core.Factory
meta import Strata.Languages.Core.Identifiers
meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core.SMTEncoder
meta import Strata.Languages.Core.Verifier

meta section

/-! # End-to-end WP/SP VC-equivalence test for Strata Core

Runs an unstructured Core program through the WP and SP verification-condition
generators in `Strata.DL.Imperative.PassiveVCGen`, then uses cvc5 to confirm that
the two generated VCs are logically equivalent (`vc_wp ⇔ vc_sp`), as Grigore et
al. show (their Remark 4 and Example 2).

The program is a diamond with a join over `int`, with a `Cmd.set` on one arm that
passification renames and reconciles at the join. Its assertion fails on the other
arm, so neither VC is valid by itself. That keeps the equivalence from holding
trivially. Three more checks keep a degenerate generator from passing:
- neither VC is constant `false` (its negation is not valid either);
- with the assertion weakened to a fact both arms establish (`¬ (y < x)`), both VCs
  are valid;
- with the assertion strengthened to one neither arm establishes (`y < x`), neither
  is valid, and they stay equivalent.

1. Build the CFG directly in Lean.
2. `PassiveVCGen.vc .wp` and `.sp` yield `vcWpE` and `vcSpE`, `Core.Expression.Expr`s.
3. Encode a VC to an SMT term and discharge its negation through cvc5
   (`validityCheck := true`): `unsat` means the VC is valid.

Passification types each incarnation from its variable's `init`, so the VCs are
encoded as they are. -/

namespace Core

section PassiveVCGenEquiv

open Lambda
open Imperative
open Imperative.PassiveVCGen

/-- The Core expression type is `Core.Expression`; its VCs are ordinary
    `LExpr`s over the Core parameters. -/
abbrev E := Core.Expression

/-! ## Example program: a diamond CFG with a join over `int` -/

/-- The Core free variables `x`, `y` and `z`, as the program writes them. -/
private def xv : E.Expr := HasFvar.mkFvar (P := E) (HasIdent.ident (P := E) "x")
private def yv : E.Expr := HasFvar.mkFvar (P := E) (HasIdent.ident (P := E) "y")
private def zv : E.Expr := HasFvar.mkFvar (P := E) (HasIdent.ident (P := E) "z")

private def md : MetaData E := .empty

/-- A diamond-shaped unstructured Core CFG over integers:

```
  entry:  init x : int := 0
          init y : int := x       -- a write, passified to `assume y@n == x@m`
          init z : int            -- unconstrained
          assert x == x           -- valid
          goto L, R
  L:      assume x < z
          y := z                  -- a second incarnation of y on this arm
          goto J
  R:      assume z < x
          goto J
  J:      assert x < y            -- holds on L, fails on R
          return
```

On `L`, `y` is `z` and `x < z`, so the assertion holds. On `R`, `y` is still `x`,
so `x < y` fails. The two incarnations of `y` meet at the join `J`, which
reconciles them. -/
private def intTy : E.Ty := LTy.forAll [] LMonoTy.int

private def ex : PCFG E :=
  { entry := "entry"
    blocks :=
      [ ("entry", mkBlock
          [ Cmd.init (HasIdent.ident (P := E) "x") intTy (.det (HasInt.zero (P := E))) md,
            Cmd.init (HasIdent.ident (P := E) "y") intTy (.det xv) md,
            Cmd.init (HasIdent.ident (P := E) "z") intTy .nondet md,
            Cmd.assert "a_entry" (HasIntOps.eq xv xv) md ]
          ["L", "R"] md),
        ("L", mkBlock
          [ Cmd.assume "u_L" (HasIntOps.lt xv zv) md,
            Cmd.set (HasIdent.ident (P := E) "y") (.det zv) md ]
          ["J"] md),
        ("R", mkBlock
          [ Cmd.assume "u_R" (HasIntOps.lt zv xv) md ]
          ["J"] md),
        ("J", mkBlock
          [ Cmd.assert "a_join" (HasIntOps.lt xv yv) md ]
          [] md) ] }

/-! ## Generated verification conditions -/

/-- The VC of `p` in calculus `m`; `ex` and the programs below are acyclic, with
    unique labels, so `vc` does not fail on them. -/
private def vcOrFalse (m : PassiveVCGen.VcMethod) (p : PCFG E) : E.Expr :=
  (PassiveVCGen.vc (P := E) m p).toOption.getD HasBool.ff

private def vcWpE : E.Expr := vcOrFalse .wp ex
private def vcSpE : E.Expr := vcOrFalse .sp ex

/-- `a ⇔ b := (a ⇒ b) ∧ (b ⇒ a)`. -/
private def iff (a b : E.Expr) : E.Expr :=
  HasBoolOps.and (HasBoolOps.imp a b) (HasBoolOps.imp b a)

/-- The biconditional whose validity we check: `vc_wp ⇔ vc_sp`. -/
private def equivE : E.Expr := iff vcWpE vcSpE

/-! ## Solver-side variable declarations

The generator emits every incarnation already typed, so `Core.toSMTTerm` accepts
the VCs directly. The free variables are still declared to the solver, all at
`int`. -/

/-- Free variables of `e`, each declared to the solver as `int`. -/
private def intVars (e : E.Expr) : List E.TypedIdent :=
  (Lambda.LExpr.LExpr.getVars e).eraseDups.map (fun v => (v, LTy.forAll [] LMonoTy.int))

/-! ## Discharge through cvc5 -/

/-- Is `e` valid? Encodes it and checks its negation with cvc5: `"valid"` when the
    solver reports `unsat`, `"invalid"` when it reports `sat` (a counterexample),
    and `"inconclusive"` for any other answer, so a timeout or `unknown` is never
    taken for either. -/
def verdict (label : String) (e : E.Expr) : IO String := do
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
                (profilePipeline := false)
  let factory := Core.Env.init.factory
  match Core.toSMTTerm factory [] e SMT.Context.default {} with
  | .error msg => throw (IO.userError s!"SMT encoding error: {msg}")
  | .ok (smtTerm, ctx, _) =>
    IO.FS.withTempDir (fun tempDir => do
      let filename := (tempDir / "passiveVcGenEquiv.smt2").toString
      let ans ← Core.SMT.dischargeObligation
        { Core.VerifyOptions.default with verbose := .quiet, solver := "cvc5" }
        (intVars e) Imperative.MetaData.empty filename
        [] smtTerm ctx
        (satisfiabilityCheck := false) (validityCheck := true)
        (label := label) (pctx := pctx)
      match ans with
      | .ok (_, .unsat, _) => return "valid"
      | .ok (_, .sat _, _) => return "invalid"
      | .ok _ => return "inconclusive"
      | .error err => throw (IO.userError s!"solver error: {err}"))

-- The assertion fails on `R`, so neither VC is valid ...
/-- info: wp: invalid, sp: invalid -/
#guard_msgs in
#eval do
  IO.println s!"wp: {← verdict "wpValid" vcWpE}, sp: {← verdict "spValid" vcSpE}"

-- ... and they are equivalent.
/-- info: wp ≡ sp: valid -/
#guard_msgs in
#eval do
  IO.println s!"wp ≡ sp: {← verdict "wpEquivSp" equivE}"

-- Neither VC is constant `false`: a satisfiable assertion has a satisfiable VC.
/-- info: wp negation: invalid, sp negation: invalid -/
#guard_msgs in
#eval do
  IO.println s!"wp negation: {← verdict "wpNeg" (HasBoolOps.not vcWpE)}, \
    sp negation: {← verdict "spNeg" (HasBoolOps.not vcSpE)}"

/-- The program with the assertion at the join replaced by `goal`. -/
private def withJoinGoal (goal : E.Expr) : PCFG E :=
  { ex with blocks := ex.blocks.map fun (l, b) =>
    if l == "J" then (l, mkBlock [ Cmd.assert "a_join" goal md ] [] md) else (l, b) }

-- A fact both arms establish: on `L`, `x < z = y`; on `R`, `y = x`. Both VCs are valid.
/-- info: wp: valid, sp: valid, wp ≡ sp: valid -/
#guard_msgs in
#eval do
  let ex' := withJoinGoal (HasBoolOps.not (HasIntOps.lt yv xv))
  let wp := vcOrFalse .wp ex'
  let sp := vcOrFalse .sp ex'
  IO.println s!"wp: {← verdict "wpValid'" wp}, sp: {← verdict "spValid'" sp}, \
    wp ≡ sp: {← verdict "equiv'" (iff wp sp)}"

-- A fact neither arm establishes: neither VC is valid, and they are still equivalent.
/-- info: wp: invalid, sp: invalid, wp ≡ sp: valid -/
#guard_msgs in
#eval do
  let ex' := withJoinGoal (HasIntOps.lt yv xv)
  let wp := vcOrFalse .wp ex'
  let sp := vcOrFalse .sp ex'
  IO.println s!"wp: {← verdict "wpValid''" wp}, sp: {← verdict "spValid''" sp}, \
    wp ≡ sp: {← verdict "equiv''" (iff wp sp)}"

end PassiveVCGenEquiv

end Core

end
