/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.Sem
public import Strata.Util.ListUtils

/-! # Rewriting goals under facts preserves failures

A goal-rewriting pass (`Pass`) walks a statement list carrying facts of some type `D`. At
each command it may rewrite the expression of an `assert` or a `cover` and computes the
facts after the command (`Pass.cmd`); after a block, an `if` or a loop it keeps what
`Pass.forget` keeps of the facts before it; facts learned inside a block or branch end with
it. No statement is added, removed or reordered.

Give the facts a meaning `γ d σ` (the facts `d` hold in the store `σ`), and say which
commands the pass handles soundly (`ok`). The pass is sound (`Sound`) when, for a factory
`F` and every command that satisfies `ok`:

* each rewritten goal has the value of the original, wherever the original has one, in
  every store where the facts hold;
* the facts after a command hold after it, given they held before and its assumptions
  hold;
* the facts after a block or `if` hold at its end, given they held before it.

A sound pass keeps the traces of a program whose commands all satisfy `ok` (`CmdsOk`),
event for event (`EvRel`): the assumptions are
the same, and each assertion or cover keeps its label and store, and its value wherever the
source condition has one. Hence a target `t` (a label and metadata) that fails in the source
fails in the output, with the rewritten condition (`Pass.fails_of_fails`). Conversely, a
failure of the output is one of the source when the source's goals have values
(`GoalsDefined`, `Pass.fails_of_fails_out`): a rewrite may give a value to a goal that has
none, as folding `1 + 2` to `3` does when the operator `+` carries no type annotation,
turning a stuck assertion into a failing one.

Key definitions: `Pass`, `Pass.stmts`, `Sound`, `CmdsOk`, `EvRel`, `GoalsDefined`.
The theorems are in `GoalRewriteProps`. -/

namespace Imperative
namespace BigStep
namespace GoalRewrite

public section

variable {P : PureExpr} {D : Type}

/-- A pass rewriting the goals of `assert`s and `cover`s under facts of type `D`. -/
structure Pass (P : PureExpr) (D : Type) where
  /-- A command, possibly with its goal rewritten, and the facts after it. -/
  cmd : D → Cmd P → Cmd P × D
  /-- What is kept of the facts across the statements given. -/
  forget : D → PStmts P → D
  /-- The facts after a call. -/
  reset : D

mutual

/-- Rewrite the goals of `s` under the facts `d`, and return the facts after it. -/
@[expose] def Pass.stmt (π : Pass P D) (d : D) : PStmt P → PStmt P × D
  | .cmd (.cmd c) =>
    let r := π.cmd d c
    (.cmd (.cmd r.1), r.2)
  | .cmd (.call n args md) => (.cmd (.call n args md), π.reset)
  | .block l ss md => (.block l (π.stmts d ss).1 md, π.forget d [.block l ss md])
  | .ite c ts es md =>
    (.ite c (π.stmts d ts).1 (π.stmts d es).1 md, π.forget d [.ite c ts es md])
  | .loop g m invs body md =>
    (.loop g m invs (π.stmts (π.forget d body) body).1 md,
      π.forget d [.loop g m invs body md])
  | .exit l md => (.exit l md, d)
  | .typeDecl tc md => (.typeDecl tc md, d)

/-- Rewrite the goals of `ss` in order, threading the facts. -/
@[expose] def Pass.stmts (π : Pass P D) (d : D) : PStmts P → PStmts P × D
  | [] => ([], d)
  | s :: rest =>
    let r := π.stmt d s
    let q := π.stmts r.2 rest
    (r.1 :: q.1, q.2)

end

/-- The command `c'` is `c`, or `c` with the expression `e` of its `assert` or `cover`
    replaced by an `e'` with `R e e'`. -/
inductive CmdRel (R : P.Expr → P.Expr → Prop) : Cmd P → Cmd P → Prop where
  | same : CmdRel R c c
  | assert : R e e' → CmdRel R (.assert l e md) (.assert l e' md)
  | cover : R e e' → CmdRel R (.cover l e md) (.cover l e' md)

/-- Two observations agree except for their expressions; the second has the value of the
    first wherever the first has one. -/
@[expose] def ArgRel (a a' : EventArg P) : Prop :=
  a.factory = a'.factory ∧ a.store = a'.store ∧ a.label = a'.label ∧
    a.metadata = a'.metadata ∧ ∀ v, P.eval a.factory a.store a.expr = some v →
      P.eval a.factory a.store a'.expr = some v

/-- Two events correspond: equal assumptions, or assertions (covers) that agree except for
    expressions, the second keeping the value of the first. -/
@[expose] def EvRel : Event P → Event P → Prop
  | .assume a, .assume a' => a = a'
  | .assert a, .assert a' => ArgRel a a'
  | .cover a, .cover a' => ArgRel a a'
  | _, _ => False

variable [HasBool P] [HasFvar P]

/-- Every assumption of the trace holds (evaluates to `true`). -/
abbrev AssumeOk (evs : List (Event P)) : Prop := Trace.AssumptionsHold P evalInterp () evs

/-- Every assertion or cover that a reach of `ss` from `σ` ends with has a condition with a
    value. A well-typed program has this property: its goals are Boolean expressions over
    its typed variables, and a well-typed expression evaluates in a store that conforms to
    the types (`LawfulHasTyping`). For Core, the program-level obligation is
    `TypeCheckWellTypes`. -/
@[expose] def GoalsDefined (F : P.Factory) (ss : PStmts P) (σ : SemanticStore P) : Prop :=
  ∀ evs ev, BReach F ss σ (evs ++ [ev]) → (∀ a, ev ≠ .assume a) →
    ∃ v, P.eval ev.condition.factory ev.condition.store ev.condition.expr = some v

mutual

/-- Every command of `ss` satisfies `ok`. -/
@[expose] def CmdsOk (ok : Cmd P → Prop) : PStmts P → Prop
  | [] => True
  | s :: rest => StmtCmdsOk ok s ∧ CmdsOk ok rest

/-- Every command of `s` satisfies `ok`. -/
@[expose] def StmtCmdsOk (ok : Cmd P → Prop) : PStmt P → Prop
  | .cmd (.cmd c) => ok c
  | .cmd (.call ..) => True
  | .block _ ss _ => CmdsOk ok ss
  | .ite _ ts es _ => CmdsOk ok ts ∧ CmdsOk ok es
  | .loop _ _ _ body _ => CmdsOk ok body
  | .exit .. | .typeDecl .. => True

end

/-- **Soundness of a goal-rewriting pass** for the factory `F`, the meaning `γ` of the facts,
    and the commands that satisfy `ok`, those the pass is sound on. Equality simplification
    takes for `ok` that a command's operators are consistent with its folding factory; other
    passes that rewrite goals, such as function inlining or simplification, can take their
    own. -/
structure Sound (F : P.Factory) (π : Pass P D) (γ : D → SemanticStore P → Prop)
    (ok : Cmd P → Prop) : Prop where
  /-- A rewritten goal has the value of the original, wherever the facts hold and the
      original has one. -/
  cmd_rel : ∀ d c, ok c → CmdRel (fun e e' => ∀ σ, γ d σ → ∀ v, P.eval F σ e = some v →
    P.eval F σ e' = some v) c (π.cmd d c).1
  /-- The facts after a command hold after it, when its assumptions hold. -/
  cmd_post : ∀ d c σ σ' evs, ok c → γ d σ → EvalCmdE P F σ c σ' evs → AssumeOk evs →
    γ (π.cmd d c).2 σ'
  /-- The facts kept across a statement that runs normally hold at its end. -/
  forget_post : ∀ d s σ evs σ', γ d σ → BRunS F s σ evs (.normal σ') → γ (π.forget d [s]) σ'


end -- public section

end GoalRewrite
end BigStep
end Imperative
