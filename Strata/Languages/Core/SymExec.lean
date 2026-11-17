/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Interpreter
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.ProgramFact

/-! # Symbolic execution on the monadic interpreter

Runs `Imperative.stepInterp` symbolically. In reading order:

* `SymExec` (this file): symbols, the symbolic evaluator (`symEval`, `symLang`), the forking
  monad and its effects (`ForkM`, `forkEffects`), and the command stepper (`symStepCmd`);
* `PathExplorer`: the path explorer (`explore`) with its path tree and merge policies, and
  the entry points for a procedure and a program (`exploreProc`, `symExecProgram`);
* `SymExecTree`: the path tree as an obligation program (`Result.treeStmts`);
* `SymExecReplay`: checking a per-path counterexample by replay (`replayObl`).

The proofs are in `SymExecProps` (this file: symbols, the evaluator, the forking monad and the
stepper) and `PathExplorerProps` (the explorer's merge).
-/

namespace Core.SymExec

open Imperative Lambda

@[expose] public section

/-! ## Symbols -/

/-- Location of the expressions symbolic execution builds itself. -/
abbrev symExecLoc : ExprSourceLoc := ExprSourceLoc.synthesized "symexec"

/-- The default prefix of fresh symbols' names; `exploreProc` lengthens it until no name the
    procedure uses starts with it (`choosePrefix`). -/
def defaultSymPrefix : String := "$__sym"

/-- Run configuration. -/
structure ExploreCfg where
  /-- Fuel for `LExpr.eval` (the simplification fuel, independent of the run fuel); by default
      the default of `Lambda.EvalConfig.fuel`. -/
  simpFuel : Nat := ({ factory := Lambda.Factory.default } : Lambda.EvalConfig CoreLParams).fuel
  /-- The symbol prefix: a name is a symbol iff it starts with it. -/
  pre : String := defaultSymPrefix
  /-- A bound on the paths of a run: once more than this many paths exist (finished, or still
      to be explored), the explorer explores no further and the paths left are `overPathLimit`
      (`explore`). `none` sets no bound. -/
  maxPaths : Option Nat := none
  /-- When set, a path ends at an `assert` whose condition evaluates to literal `false` (after
      recording it), and at an `assume` that contradicts the path condition (literal `false`,
      or the negation of a condition already assumed, `pcRefutes`); see `failedCheckStatus`.
      Off by default: a path continues past a failed assert, so the checks after it still get
      their own verdicts. -/
  endOnFailedChecks : Bool := false

/-- Whether `x` is a symbol: its name starts with `pre`. Decided from the name alone, since the
    evaluator does not see the path state; `exploreProc` chooses `pre` so that no name the
    procedure uses starts with it (`choosePrefix_fresh`). -/
def isSymName (pre : String) (x : CoreIdent) : Bool := x.name.startsWith pre

/-- The `k`-th symbol, annotated with its type, for the variable `name` (`""` for none): named
    `pre ++ name ++ "_" ++ k`, or `pre ++ k` without a name, so a model names the input it
    gives a value to. The name stays unique: the text after `pre` ends in `k` (after the last
    `_` when there is a name, and is all of it otherwise), and the explorer never creates the same
    `k` twice. -/
def mkSym (pre : String) (k : Nat) (ty : LMonoTy) (name : String := "") : Expression.Expr :=
  .fvar symExecLoc
    ⟨if name.isEmpty then pre ++ toString k else pre ++ name ++ "_" ++ toString k, ()⟩ (some ty)

/-- The shortest extension of `defaultSymPrefix` by underscores that no name in `names` starts
    with. The fuel, one more than the longest name's length, suffices: a name starts only with
    prefixes no longer than itself. -/
def choosePrefix (names : List String) : String :=
  let maxLen := names.foldl (fun m n => max m n.length) 0
  let rec go : Nat → String → String
    | 0, p => p
    | n + 1, p => if names.any (·.startsWith p) then go n (p ++ "_") else p
  go (maxLen + 1) defaultSymPrefix

/-! ## The symbolic evaluator -/

/-- Evaluate `e` at the simplification fuel with the store as environment: stored values
    replace program variables, symbols stay, and built-in calls on values fold. The result is
    kept even if the fuel runs out. `none` if `e` mentions a program variable the store does
    not bind. -/
def symEval (cfg : ExploreCfg) (F : Lambda.Factory CoreLParams) (σ : RStore Expression)
    (e : Expression.Expr) : Option Expression.Expr :=
  -- Checked on the input, not the result: stored values mention only symbols (every stored
  -- value is built from `symEval` results, fresh symbols and merge `if`s), so the result
  -- mentions a program variable only if `e` mentions one the store does not bind.  This keeps
  -- the check proportional to `e` rather than to the (growing) stored terms.
  if (LExpr.freeVars e).all (fun p => isSymName cfg.pre p.1 || (σ p.1).isSome) then
    some (LExpr.eval cfg.simpFuel F σ e).1
  else none

/-- The message for a `symEval` failure: the program variables of `e` that are neither symbols
    nor bound in the store. -/
def symEvalFailure (pre : String) (σ : RStore Expression) (e : Expression.Expr) : String :=
  let unbound := (LExpr.freeVars e).filterMap fun p =>
    if isSymName pre p.1 || (σ p.1).isSome then none else some p.1.name
  s!"unbound program variable(s): {", ".intercalate unbound.eraseDups}"

/-- Core's interpreter language data for symbolic runs: `boundedEval` is `symEval`, `isValue`
    accepts every term, and `hasType`/`sameType` always hold. `typeOf` (the type `x := *` draws
    at) is Core's, which reads type annotations; symbols are annotated (`mkSym`). Not an
    instance: pass it explicitly (`letI`). -/
@[reducible] def symLang (cfg : ExploreCfg) : InterpLang Expression :=
  { (inferInstance : InterpLang Expression) with
    -- No per-step type checks: Core's `hasType`/`sameType` type-check the whole value before
    -- and after the update, which for symbolic terms grows with the run (quadratic on
    -- straight-line code).
    -- The program is type-checked before VC generation (`typeAnnotated`), which already
    -- guarantees what these checks would.
    ops := { isValue := fun _ _ => true, hasType := fun _ _ _ => true,
             sameType := fun _ _ _ => true }
    boundedEval := fun _ => symEval cfg }

/-! ## The forking monad -/

/-- What an obligation checks. -/
inductive OblKind where
  | assert
  | cover
  deriving Repr, BEq, DecidableEq

/-- One entry in a path's record of choices: the fresh symbols its havocs (`x := *`) created,
    which replay uses to rebuild the run a model describes:
    * `sym x`: the symbol `x`, the answer to one `choose`;
    * `merge g t e`: a merge of two branches with guard `g`; `t` and `e` are the then- and
      else-branch's own entries, oldest first. Replay keeps the entries of the branch `g`
      takes under the model. -/
inductive Choice where
  | sym (x : Expression.Expr)
  | merge (guard : Expression.Expr) (thenChoices elseChoices : List Choice)

/-- An obligation from an `assert` or a `cover` (`kind`): its condition `cond` under the path
    condition `pc` (newest first). -/
structure Obl where
  kind : OblKind
  label : String
  pc : List (String × Expression.Expr)
  cond : Expression.Expr
  md : MetaData Expression
  /-- The path's record of choices before the check, newest first: the oracle a replay of this
      path consumes. -/
  choices : List Choice := []
  /-- Whether the path went through a merge (then it stands for several runs). -/
  merged : Bool := false

/-- The per-path state. -/
structure PathState where
  /-- The next fresh symbol index.  The explorer seeds it from its own counter before every step,
      so sibling paths never create the same name. -/
  next : Nat := 0
  /-- The path condition, newest first. -/
  pc : List (String × Expression.Expr) := []
  /-- Obligations recorded on this path since the explorer last flushed them, newest first. -/
  segment : List Obl := []
  /-- The path's record of choices, newest first. -/
  choices : List Choice := []
  /-- Whether the path went through a merge. -/
  merged : Bool := false

/-- One outcome of a path. -/
inductive Out (α : Type) where
  | ok (a : α)
  /-- The path stopped (out of fuel, unsupported construct, program error). -/
  | stop (r : StopReason)

/-- The forking monad: each computation has a list of outcomes, each with its path state. -/
abbrev ForkM (α : Type) : Type := ExploreCfg → PathState → List (Out α × PathState)

instance : Monad ForkM where
  pure a := fun _ st => [(.ok a, st)]
  bind x f := fun cfg st => (x cfg st).flatMap fun (o, st') =>
    match o with
    | .ok a => f a cfg st'
    | .stop r => [(.stop r, st')]

instance : MonadExcept StopReason ForkM where
  throw r := fun _ st => [(.stop r, st)]
  tryCatch x h := fun cfg st => (x cfg st).flatMap fun (o, st') =>
    match o with
    | .stop r => h r cfg st'
    | o => [(o, st')]

/-- The negation of a guard, written `if c then false else true`; path conditions and
    obligations keep that shape. -/
def negate (c : Expression.Expr) : Expression.Expr := .ite symExecLoc c Core.false Core.true

/-- Whether the path condition `pc` contains `c`, up to source locations
    (`LExpr.beqIgnoringMetadata`).  Syntactic. -/
def pcContains (pc : List Expression.Expr) (c : Expression.Expr) : Bool :=
  pc.any (·.beqIgnoringMetadata c)

/-- Whether the path condition `pc` contains the negation of `c`, in either direction
    (`negate c ∈ pc`, or `c = negate d` for some `d ∈ pc`), up to source locations.
    Syntactic. -/
def pcRefutes (pc : List Expression.Expr) (c : Expression.Expr) : Bool :=
  pc.any fun d => d.beqIgnoringMetadata (negate c) || c.beqIgnoringMetadata (negate d)

/-- The conditions of a path condition, without their labels. -/
def pcExprs (pc : List (String × Expression.Expr)) : List Expression.Expr := pc.map (·.2)

/-- Add `c` to the path condition under `label`, the `assume`'s label, which the obligations
    keep. Literal `true`, and `c` already present under the same label, are not added (both up
    to source locations); `c` present under another label is added again under this one. A
    contradicting condition (literal `false`, or the negation of one already assumed) does not
    end the path: later checks are still recorded, under a path condition that implies `false`
    (an assert holds, a cover fails). -/
def assumeCond (label : String) (c : Expression.Expr) : ForkM Unit := fun _ st =>
  if c.beqIgnoringMetadata Core.true ||
      st.pc.any (fun (l, d) => l == label && d.beqIgnoringMetadata c) then [(.ok (), st)]
  else [(.ok (), { st with pc := (label, c) :: st.pc })]

/-- Evaluate an event's condition at the configured simplification fuel. -/
def evalCond (arg : REventArg Expression (Lambda.Factory CoreLParams)) : ForkM Expression.Expr :=
  fun cfg st =>
  match symEval cfg arg.factory arg.store arg.expr with
  | some c => [(.ok c, st)]
  | none =>
    [(.stop (.interrupted (symEvalFailure cfg.pre arg.store arg.expr)), st)]

/-- Record an obligation on the current path. -/
def record (kind : OblKind) (arg : REventArg Expression (Lambda.Factory CoreLParams))
    (c : Expression.Expr) : ForkM Unit :=
  fun _ st =>
    [(.ok (), { st with segment := { kind, label := arg.label, pc := st.pc, cond := c,
                                     md := arg.metadata, choices := st.choices,
                                     merged := st.merged } :: st.segment })]

/-- `ForkM`'s effects, for the symbolic language data of configuration `c` (the effects interface
    is indexed by the language data). `choose` names its symbol after `name`, the variable it
    draws a value for (`""` for none: a nondeterministic guard). Pass explicitly (`letI`). -/
@[reducible] def forkEffects (c : ExploreCfg) (name : String := "") :
    @InterpEffects Expression (symLang c) ForkM :=
  letI := symLang c
  {
    choose _ _ ty := fun cfg st =>
      match ty.toMonoType? with
      | some mty =>
        let x := mkSym cfg.pre st.next mty name
        [(.ok x, { st with next := st.next + 1, choices := .sym x :: st.choices })]
      | none => [(.stop .illTypedValue, st)]
    emit ev := match ev with
      | .assume arg => do assumeCond arg.label (← evalCond arg)
      | .assert arg => do record .assert arg (← evalCond arg)
      | .cover arg => do record .cover arg (← evalCond arg)
    branch _ _ g := fun _ st =>
      if pcContains (pcExprs st.pc) g then [(.ok true, st)]
      else if pcRefutes (pcExprs st.pc) g then [(.ok false, st)]
      else
        -- A fork gives one outcome the guard and the other its negation, as path-condition
        -- entries labeled `<label_ite_cond_true: g>` and `<label_ite_cond_false: !(g)>` over the
        -- evaluated guard; obligations keep these labels. Both outcomes copy the rest of the
        -- path state, which is safe because nothing has been recorded yet in this step: `if`
        -- and loops branch before anything else, and the explorer starts each step with an empty
        -- `segment`.
        let lt := toString f!"<label_ite_cond_true: {g.eraseTypes}>"
        let lf := toString f!"<label_ite_cond_false: !({g.eraseTypes})>"
        [(.ok true, { st with pc := (lt, g) :: st.pc }),
         (.ok false, { st with pc := (lf, negate g) :: st.pc })] }

/-! ## The command stepper -/

/-- The variable a base command draws a nondeterministic value for (`x := *`, or `var x` without
    a value), else `""`. -/
def havocName : Imperative.Cmd Expression → String
  | .init x _ .nondet _ | .set x .nondet _ => x.name
  | _ => ""

/-- One base command through the engine's generic stepper, with `choose` naming its symbol
    after the variable the command havocs (`havocName`). -/
def stepBase (cfg : ExploreCfg) (fuel : Nat) (env : @IEnv Expression (symLang cfg))
    (base : Imperative.Cmd Expression) : ForkM (@IStore Expression (symLang cfg)) :=
  letI := symLang cfg
  letI := forkEffects cfg (havocName base)
  stepBaseCmdStore fuel env.factory env.store base

/-- Steps Core commands under `symLang cfg`: base commands through the engine's generic stepper
    (`stepBase`). A call stops its path: the pipeline eliminates calls first
    (`symExecRequires`). -/
def symStepCmd (cfg : ExploreCfg) : @StepCmdM Expression (symLang cfg) Command ForkM :=
  letI := symLang cfg
  fun fuel env cmd =>
    match cmd with
    | .cmd base => do
      let store ← stepBase cfg fuel env base
      return .terminal { env with store }
    | .call _ _ _ => throw (.interrupted "call (eliminate calls first)")

end -- public section

end Core.SymExec
