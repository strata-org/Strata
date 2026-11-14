/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Util.ListUtils
public import Strata.DL.Lambda.LExprType

/-! # The formulas of a declaration

The formulas each declaration contributes to the declarations entry (`declFormulas`), and the
per-program checks on them that the deductive-verification theorems take as hypotheses
(`Program.formulasTypedB`, `Program.distinctsBeforeLemmasB`). They depend only on the
program's syntax, so they are stated apart from the deductive-verification statements and
can be used by modules those statements import.
-/

public section

namespace Core.Specification.Analysis

open Core

/-- That `a` and `b` are different: false when they are equal, true otherwise. -/
@[expose] def distinctPairExpr (a b : Expression.Expr) : Expression.Expr :=
  .ite Core.coreLoc (.eq Core.coreLoc a b) (.boolConst Core.valueLoc false) (.boolConst Core.valueLoc true)

/-- The formulas declaration `d` contributes to the declarations entry: an axiom's and a
    lemma's formula, and the disequality of each pair of a `distinct` declaration's
    expressions (`distinctPairExpr`). -/
@[expose] def declFormulas : Decl → List Expression.Expr
  | .ax a _ => [a.e]
  | .lemma l _ => [l.e]
  | .distinct _ es _ => es.orderedPairs.map fun (a, b) => distinctPairExpr a b
  | _ => []

/-- **Every formula of declaration `d` is a closed Boolean expression**: it has no free
    variable and has type `bool` under its own annotations. For a `distinct` declaration this
    says its expressions have one type, since `distinctPairExpr a b` compares `a` with `b`.
    Such a formula has a value in every model, under every store
    (`declFormulasTyped_eval_isSome`). -/
@[expose] def declFormulasTyped (d : Decl) : Bool :=
  (declFormulas d).all fun e =>
    e.freeVars.isEmpty && Lambda.LExpr.typeCheck [] e == some .bool

/-- **Every formula of every declaration of `p` is a closed Boolean expression**
    (`declFormulasTyped`), as a check on the program. -/
@[expose] def Program.formulasTypedB (p : Program) : Bool :=
  p.decls.all declFormulasTyped

/-- **Every `distinct` declaration of `p` comes before every lemma.** On such a program the
    declarations entry and `Core.verify` assume the same `distinct` facts for each lemma.
    `Core.verify` assumes every `distinct` declaration for every lemma, also the later ones,
    so a theorem that reads its lemma verdicts as deductive verification over the
    declarations entry takes this as a hypothesis. -/
@[expose] def Program.distinctsBeforeLemmasB (p : Program) : Bool :=
  (p.decls.dropWhile fun d => d.kind != .lemma).all fun d => d.kind != .distinct

end Core.Specification.Analysis

end -- public section
