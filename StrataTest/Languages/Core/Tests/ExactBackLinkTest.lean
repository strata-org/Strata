/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Core.Tests.CounterexampleTestUtils
meta import Strata.Languages.Core.Counterexample.BackLinkExactProps
meta import Strata.Languages.Core.Counterexample.BackLinkChainReplay
meta import Strata.Languages.Core.Counterexample.BackLinkExactNondet
meta import Strata.Languages.Core.Counterexample.BackLinkExactInsert
meta import Strata.Transform.CoreTransform
meta import Strata.Transform.InsertLoopInvariantAsserts
meta import Strata.Transform.PrecondElim
meta import Strata.Transform.LoopElim
meta import Strata.Languages.Core.Counterexample.BackLinkPhases

/-! # Replay-free exact back-links (`Core.exactBackLink`) unit tests

For each certified exact phase: a downstream chain (unconfirmed slices and a claim)
is translated upstream by `exactBackLink` — a pure translation, no replay — and the
translated claim is then replayed upstream to check that it is indeed genuine and
feasible (the executable counterpart of the certificate's `claim_back`).

`filterProcedures`: the downstream procedure table resolves only `Copy`; the
upstream table also resolves `Other` (a procedure the filter removed).  The unit is
`call Copy(5, out y); assert tgt (y == 6)`. -/

meta section

namespace ExactBackLinkTest

open Core Lambda Imperative
open Core.CexTestUtils

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def yVar : Expression.Expr := .fvar default (id "y") (some .int)

/-- `Copy(n : int, out result : int) { result := n; }`. -/
private def copyProc : Procedure := {
  header := { name := id "Copy", typeArgs := [],
              inputs := [(id "n", (.int : Lambda.LMonoTy))],
              outputs := [(id "result", (.int : Lambda.LMonoTy))] }
  spec := { preconditions := [], postconditions := [] }
  body := .structured
    [ .cmd (.cmd (.set (id "result") (.det (.fvar default (id "n") (some .int))) md)) ] false }

/-- A procedure only the upstream program has. -/
private def otherProc : Procedure :=
  { copyProc with header := { copyProc.header with name := id "Other" } }

/-- Downstream (filtered) table. -/
private def piDown : String → Option Procedure :=
  fun n => if n == "Copy" then some copyProc else none
/-- Upstream table: a super-table of `piDown`. -/
private def piUp : String → Option Procedure :=
  fun n => if n == "Copy" then some copyProc else if n == "Other" then some otherProc else none

private def callStmt : Statement :=
  .cmd (CmdExt.call "Copy" none [.inArg (int 5), .outArg (id "y")] md)
private def assertTgt : Statement :=
  .cmd (.cmd (.assert "tgt" (.eq default yVar (int 6)) md))
private def tgt : AssertId Expression := { label := "tgt", md := md }

private def unit : List Statement := [callStmt, assertTgt]

private def env (y : Int) : IEnv Expression :=
  .ofStore (fun n => if n == id "y" then some (int y) else none) Core.Factory

/-- `piDown` is a sub-table of `piUp`: every procedure `piDown` resolves, `piUp` resolves
    to the same procedure. -/
private theorem hsub : ∀ n p, piDown n = some p → piUp n = some p := by
  intro n p h
  simp only [piDown, piUp] at h ⊢
  split at h <;> simp_all

private def cert := ExactCert.ofSubTable hsub
private def link := exactBackLink "filterProcedures" cert

/-- Whether the production (enforcing) replay of `c` at fuel `f` under `π` reports the
    target `t` as genuinely failing: the check `genuineEnforced` states. -/
private def enforcedGenuineAt (t : AssertId Expression) (π : String → Option Procedure)
    (c : CexA Expression Command) (f : Nat) : Bool :=
  match (runReplay (runCoreInterp (m := ReplayM Expression) π f c.cfg)
      { oracleConfig := .strict, interruptOn := enforceInterrupt t f }
      (assertFailureHalt t f) c.oracle).1 with
  | .genuine => true
  | _ => false

/-- `enforcedGenuineAt` for the target `tgt`. -/
private def enforcedGenuine := enforcedGenuineAt tgt

/-- Whether a validation verdict is `.genuine`. -/
private def isGenuine : CEValidationVerdict StopReason → Bool
  | .genuine => true | _ => false

/-! ### A lone top-level claim -/

private def topClaim : CexA Expression Command := { cfg := .stmts unit (env 0), oracle := [] }
private def outTop : BackLinkOutcome Expression Command := ⟨[], some (topClaim, replayFuelGuess)⟩

-- The downstream claim is genuine and feasible downstream.
#guard isGenuine (replayWithM topClaim tgt replayFuelGuess piDown)
#guard enforcedGenuine piDown topClaim replayFuelGuess

-- Translated with no replay: still a lone top-level claim, same fuel.
#guard summary (link.lift unit outTop) == ([], some (some unit, replayFuelGuess, []))
-- Spot check of `claim_back`: the translated claim replays genuinely upstream.
#guard match (link.lift unit outTop).claim with
  | some (c, f) => isGenuine (replayWithM c tgt f piUp) && enforcedGenuine piUp c f
  | none => false

/-! ### An empty source unit

A unit the phase synthesized, or a procedure with a CFG body, has an empty source unit.
The replay back-links lift nothing into it: the downstream claim `topClaim` is not passed
up as a claim about the source. -/

#guard summary ((nondetElimBackLink piDown tgt).lift [] outTop) == ([], none)
#guard summary ((stmtsToCFGBackLink piDown tgt).lift [] outTop) == ([], none)
#guard summary (slicedChainOutcome piDown tgt [] _root_.id
    (fun c => { slices := [c], claim := none }) some outTop) == ([], none)
-- On the non-empty unit the same incoming claim is lifted to a lone top-level claim.
#guard summary ((nondetElimBackLink piDown tgt).lift unit outTop) ==
  ([], some (some unit, replayFuelGuess, []))

/-- The base-command unit `assert tgt (y == 6)`. -/
private def baseUnit : List (Stmt Expression (Cmd Expression)) :=
  [.cmd (.assert "tgt" (.eq default yVar (int 6)) md)]
/-- A lone top-level claim at the base representation, in the store `y = 0`. -/
private def outTopBase : BackLinkOutcome Expression (Cmd Expression) :=
  ⟨[], some ({ cfg := .stmts baseUnit (env 0), oracle := [] }, replayFuelGuess)⟩

-- The loop-init hoist back-link also lifts nothing into an empty source unit.
#guard let o := (hoistBackLink tgt).lift [] outTopBase; o.slices.isEmpty && o.claim.isNone
-- On the non-empty base unit it lifts the incoming claim to a lone top-level claim: the
-- base unit itself in the store `y = 0`, with no oracle, at the guessed fuel.
#guard let o := (hoistBackLink tgt).lift baseUnit outTopBase
  o.slices.isEmpty && match o.claim with
    | some ({ cfg := .stmts ss e, oracle }, f) =>
      ss == baseUnit && e.store.get (id "y") == some (int 0) && oracle.isEmpty
        && f == replayFuelGuess
    | _ => false

/-! ### An unconfirmed top slice, a gap, and a non-top claim -/

private def gapSlice : CexA Expression Command := { cfg := .stmts [callStmt] (env 1), oracle := [] }
private def innerClaim : CexA Expression Command :=
  { cfg := .stmts [assertTgt] (env 5), oracle := [] }
private def outGaps : BackLinkOutcome Expression Command :=
  ⟨[topClaim, gapSlice], some (innerClaim, replayFuelGuess)⟩

#guard enforcedGenuine piDown innerClaim replayFuelGuess
-- Every slice and the claim are translated; the gaps are preserved (no merging).
#guard summary (link.lift unit outGaps) ==
  ([some unit, some [callStmt]], some (some [assertTgt], replayFuelGuess, []))
#guard match (link.lift unit outGaps).claim with
  | some (c, f) => !isTopLevelAtB unit c.cfg && f == replayFuelGuess
      && isGenuine (replayWithM c tgt f piUp) && enforcedGenuine piUp c f
  | none => false

/-! ### Fuel monotonicity (`genuineFeasible_fuel_mono`), executably -/

#guard enforcedGenuine piUp topClaim (2 * replayFuelGuess)

/-! ### `termCheck` on an existing procedure (single table, unit unchanged) -/

private def tcLink :=
  exactBackLink "termCheck" (ExactCert.ofSubTable (π' := piUp) (π := piUp) fun _ _ h => h)

#guard summary (tcLink.lift unit outGaps) ==
  ([some unit, some [callStmt]], some (some [assertTgt], replayFuelGuess, []))
#guard match (tcLink.lift unit outGaps).claim with
  | some (c, f) => !isTopLevelAtB unit c.cfg && f == replayFuelGuess
      && isGenuine (replayWithM c tgt f piUp) && enforcedGenuine piUp c f
  | none => false
#guard summary (tcLink.lift unit outTop) == ([], some (some unit, replayFuelGuess, []))

/-! ### `nondetElim` (relational certificate)

Upstream unit: `ite * { assert tgt2 (x == 1) } {}` with `x = 2`.  Downstream:
`init $__ndelim_ite$_0 := *; ite ($__ndelim_ite$_0) { assert tgt2 (x == 1) } {}`.  The
oracle `[tt]` takes the then-branch on both sides. -/

private def xVar : Expression.Expr := .fvar default (id "x") (some .int)
private def assertTgt2 : Statement := .cmd (.cmd (.assert "tgt2" (.eq default xVar (int 1)) md))
private def tgt2 : AssertId Expression := { label := "tgt2", md := md }
private def ndUnit : List Statement := [.ite .nondet [assertTgt2] [] md]
private def ndUnit' : List Statement := Block.nondetElim ndUnit
private def envX : IEnv Expression :=
  .ofStore (fun n => if n == id "x" then some (int 2) else none) Core.Factory

private def ndLink := exactBackLink "nondetElim" (nondetElimCert piUp piUp)

/-- `enforcedGenuineAt` for the target `tgt2`. -/
private def enforcedGenuine2 := enforcedGenuineAt tgt2

-- The downstream unit is the rewritten one (an `init` of a fresh name, then a det `ite`
-- whose guard is that name, compared up to metadata).
#guard match ndUnit' with
  | [s, .ite (.det g) [a] [] m] =>
    s == .cmd (.cmd (.init (id "$__ndelim_ite$_0") (.forAll [] .bool) .nondet md)) &&
      g =ₘ .fvar default (id "$__ndelim_ite$_0") (some .bool) && a == assertTgt2 && m == md
  | _ => false
#guard ndListB ndUnit' ndUnit

private def ndTop : CexA Expression Command :=
  { cfg := .stmts ndUnit' envX, oracle := [HasBool.tt (P := Expression)] }
private def ndOutTop : BackLinkOutcome Expression Command := ⟨[], some (ndTop, replayFuelGuess)⟩

-- The downstream claim is genuine and feasible downstream.
#guard enforcedGenuine2 piUp ndTop replayFuelGuess

-- Translated with no replay: a lone top-level claim at the upstream unit, same fuel and oracle.
#guard summary (ndLink.lift ndUnit ndOutTop) ==
  ([], some (some ndUnit, replayFuelGuess, [HasBool.tt (P := Expression)]))
-- Spot check of `claim_back`: the translated claim replays genuinely upstream.
#guard match (ndLink.lift ndUnit ndOutTop).claim with
  | some (c, f) => enforcedGenuine2 piUp c f
  | none => false

-- A chain with a gap: an unconfirmed top slice, a gap slice, and a non-top claim.
private def ndGap : CexA Expression Command := { cfg := .stmts [] envX, oracle := [] }
private def ndInner : CexA Expression Command := { cfg := .stmts [assertTgt2] envX, oracle := [] }
private def ndOutGaps : BackLinkOutcome Expression Command :=
  ⟨[{ ndTop with oracle := [] }, ndGap], some (ndInner, replayFuelGuess)⟩

#guard enforcedGenuine2 piUp ndInner replayFuelGuess
#guard summary (ndLink.lift ndUnit ndOutGaps) ==
  ([some ndUnit, some []], some (some [assertTgt2], replayFuelGuess, []))
#guard match (ndLink.lift ndUnit ndOutGaps).claim with
  | some (c, f) => !isTopLevelAtB ndUnit c.cfg && f == replayFuelGuess && enforcedGenuine2 piUp c f
  | none => false

-- The syntactic inverse reads a fresh guard's `init` and `if` back as `if *`; on the same shape
-- with a user variable `b` it is the identity, which `ndListB` accepts.
#guard undoNdL ndUnit' == ndUnit
private def userInitIf : List Statement :=
  [.cmd (.cmd (.init (id "b") (.forAll [] .bool) .nondet md)),
   .ite (.det (.fvar default (id "b") (some .bool))) [assertTgt2] [] md]
#guard undoNdL userInitIf == userInitIf
#guard ndListB userInitIf (undoNdL userInitIf)

-- A non-top claim whose statement list holds a rewritten pair: the unit `assume pre; ite * …`
-- and the claim at the downstream tail `init …; ite (…) …`, translated by the inverse.
private def preS : Statement := .cmd (.cmd (.assume "pre" (HasBool.tt (P := Expression)) md))
private def ndUnitP : List Statement := preS :: ndUnit
private def ndInnerP : CexA Expression Command :=
  { cfg := .stmts ((Block.nondetElim ndUnitP).drop 1) envX, oracle := [HasBool.tt (P := Expression)] }
private def ndOutInnerP : BackLinkOutcome Expression Command :=
  ⟨[{ cfg := .stmts (Block.nondetElim ndUnitP) envX, oracle := [] }], some (ndInnerP, replayFuelGuess)⟩
#guard summary (ndLink.lift ndUnitP ndOutInnerP) ==
  ([some ndUnitP], some (some ndUnit, replayFuelGuess, [HasBool.tt (P := Expression)]))
#guard match (ndLink.lift ndUnitP ndOutInnerP).claim with
  | some (c, f) => !isTopLevelAtB ndUnitP c.cfg && enforcedGenuine2 piUp c f
  | none => false

/-! ### Insertion phases (relational certificate `insCert`)

Each unit is run through the actual transform (as the body of a procedure `P`); the
downstream claim is translated to the input unit with no replay and then replayed
upstream. -/

/-- A program with one procedure `P`, without parameters or contract, whose body is `body`. -/
private def procOf (body : List Statement) : Program :=
  { decls := [.proc { header := { name := id "P", typeArgs := [], inputs := [], outputs := [] }
                      spec := { preconditions := [], postconditions := [] }
                      body := .structured body false } #[]] }

/-- The structured body of a program's single procedure, `[]` for any other program. -/
private def bodyOf (p : Program) : List Statement :=
  match p.decls with
  | [.proc proc _] => match proc.body with | .structured ss _ => ss | _ => []
  | _ => []

private def iVar : Expression.Expr := .fvar default (id "i") (some .int)
private def intTy : Expression.Ty := .forAll [] .int

/-! #### `insertLoopInvariantAsserts` (a loop with an invariant, no measure)

`i := 0; while (i < 2) invariant (i == i) { i := i + 1 }; assert tgt3 (i == 5)`. -/

private def loopUnit : List Statement :=
  [ .cmd (.cmd (.init (id "i") intTy (.det (int 0)) md)),
    .loop (.det (.app default (.app default Core.intLtOp iVar) (int 2))) none
      [("inv", .eq default iVar iVar)]
      [.cmd (.cmd (.set (id "i")
        (.det (.app default (.app default Core.intAddOp iVar) (int 1))) md))] md,
    .cmd (.cmd (.assert "tgt3" (.eq default iVar (int 5)) md)) ]
private def tgt3 : AssertId Expression := { label := "tgt3", md := md }

private def loopUnit' : List Statement :=
  match Core.Transform.run (procOf loopUnit) insertLoopInvariantAsserts with
  | .ok (_, p) => bodyOf p
  | .error _ => []

private def envEmpty : IEnv Expression :=
  .ofStore (fun _ => none) Core.Factory

-- The phase inserted asserts/assumes (and stripped the invariant); the checker relates the
-- two units.
#guard loopUnit'.length == 7
#guard insListB loopInvExt loopUnit' loopUnit

private def liLink :=
  exactBackLink "insertLoopInvariantAsserts" (insCert loopInvExt piUp piUp (fun st => some st))

private def liTop : CexA Expression Command := { cfg := .stmts loopUnit' envEmpty, oracle := [] }
private def liOut : BackLinkOutcome Expression Command := ⟨[], some (liTop, replayFuelGuess)⟩

#guard enforcedGenuineAt tgt3 piUp liTop replayFuelGuess
#guard summary (liLink.lift loopUnit liOut) == ([], some (some loopUnit, replayFuelGuess, []))
#guard match (liLink.lift loopUnit liOut).claim with
  | some (c, f) => isTopLevelAtB loopUnit c.cfg && enforcedGenuineAt tgt3 piUp c f
  | none => false

-- A chain with a gap, the claim inside the unit (just before the final assert).
private def liInner : CexA Expression Command :=
  { cfg := .stmts [.cmd (.cmd (.assert "tgt3" (.eq default iVar (int 5)) md))]
      { envEmpty with store := .ofStore fun n => if n == id "i" then some (int 2) else none },
    oracle := [] }
private def liGaps : BackLinkOutcome Expression Command :=
  ⟨[liTop, { cfg := .stmts [] envEmpty, oracle := [] }], some (liInner, replayFuelGuess)⟩

#guard summary (liLink.lift loopUnit liGaps) ==
  ([some loopUnit, some []], some (stmtsOf liInner.cfg, replayFuelGuess, []))
#guard match (liLink.lift loopUnit liGaps).claim with
  | some (c, f) => !isTopLevelAtB loopUnit c.cfg && enforcedGenuineAt tgt3 piUp c f
  | none => false

/-! #### `insertLoopInvariantAsserts` (a loop with a measure)

`i := 0; while (i < 3) decreases (3 - i) { i := i + 1; assert tgtM (i < 3) }`.  The phase
inserts `init m_old := *; assume m_old == 3 - i; assert ¬(m_old < 0)` at the top of the
body and `assert (3 - i) < m_old` at its bottom; `tgtM` fails at the third iteration. -/

private def lt3 : Expression.Expr := .app default (.app default Core.intLtOp iVar) (int 3)
private def measI : Expression.Expr := .app default (.app default Core.intSubOp (int 3)) iVar
private def incI : Statement :=
  .cmd (.cmd (.set (id "i") (.det (.app default (.app default Core.intAddOp iVar) (int 1))) md))
private def mUnit : List Statement :=
  [ .cmd (.cmd (.init (id "i") intTy (.det (int 0)) md)),
    .loop (.det lt3) (some measI) [] [incI, .cmd (.cmd (.assert "tgtM" lt3 md))] md ]
private def tgtM : AssertId Expression := { label := "tgtM", md := md }

private def mUnit' : List Statement :=
  match Core.Transform.run (procOf mUnit) insertLoopInvariantAsserts with
  | .ok (_, p) => bodyOf p
  | .error _ => []

-- The phase inserted the measure snapshot (`init m_old := D`, a reserved name), so the
-- plain insertion checker rejects the unit; the measured-loop checker relates it.
#guard !insListB loopInvExt mUnit' mUnit
#guard measListB loopInvExt mUnit' mUnit

private def mLink := exactBackLink "insertLoopInvariantAsserts"
  (insCert loopInvExt piUp piUp (fun st => some st))
private def mTop (oracle : List Expression.Expr) : CexA Expression Command :=
  { cfg := .stmts mUnit' envEmpty, oracle := oracle }

-- The downstream chain `loopElim`'s slicer produces: the pre-loop slice, cut at the loop
-- entry (mid-loop state `i = 2` from the oracle), and the claim at the iteration start.
-- The snapshot is deterministic, so the claim's oracle holds nothing for it.
private def mSliced := loopElimSlice piUp tgtM (mTop [int 2])
private def mOut : BackLinkOutcome Expression Command := ⟨mSliced.slices, mSliced.claim⟩

#guard summary ⟨mSliced.slices, mSliced.claim⟩ == ([some mUnit'], some (none, replayFuelGuess, []))
#guard match mSliced.claim with
  | some (c, f) => c.oracle.isEmpty && !measIterDraws loopInvExt c.cfg &&
      enforcedGenuineAt tgtM piUp c f
  | none => false
-- Translated with no replay: the chain keeps both elements, the claim's oracle is kept,
-- and replaying the translated claim upstream is genuine.
#guard summary (mLink.lift mUnit mOut) == ([some mUnit], some (none, replayFuelGuess, []))
#guard match (mLink.lift mUnit mOut).claim with
  | some (c, f) => c.oracle.isEmpty && !isTopLevelAtB mUnit c.cfg && enforcedGenuineAt tgtM piUp c f
  | none => false

-- A claim from the iteration start of `i = 0`, spanning all three iterations (as a
-- chain-replay merge produces): the downstream run takes three snapshots and draws nothing;
-- the translated claim is still genuine upstream.
private def mIter0 : CexA Expression Command :=
  { cfg := match mSliced.claim with
      | some (c, _) => match c.cfg with
        | .seq (.seq (.block none σ (.stmts ss env)) l) rest =>
          .seq (.seq (.block none σ (.stmts ss
            { env with
              store := .ofStore fun n =>
                if n == id "i" then some (int 0) else env.store.get n })) l)
              rest
        | cfg => cfg
      | none => .stmts [] envEmpty,
    oracle := [] }
private def mMerged : BackLinkOutcome Expression Command :=
  ⟨mSliced.slices, some (mIter0, replayFuelGuess)⟩
#guard enforcedGenuineAt tgtM piUp mIter0 replayFuelGuess
#guard summary (mLink.lift mUnit mMerged) == ([some mUnit], some (none, replayFuelGuess, []))
#guard match (mLink.lift mUnit mMerged).claim with
  | some (c, f) => c.oracle.isEmpty && enforcedGenuineAt tgtM piUp c f
  | none => false

-- The measured loop's body also draws (`init z := *`): the upstream run would read its
-- oracle, so the certificate declines the unit (the wiring falls back to the direct link).
private def ndUnitM : List Statement :=
  [ .cmd (.cmd (.init (id "i") intTy (.det (int 0)) md)),
    .loop (.det lt3) (some measI) []
      [.cmd (.cmd (.init (id "z") intTy .nondet md)), incI,
          .cmd (.cmd (.assert "tgtM" lt3 md))] md ]
private def ndUnitM' : List Statement :=
  match Core.Transform.run (procOf ndUnitM) insertLoopInvariantAsserts with
  | .ok (_, p) => bodyOf p
  | .error _ => []
private def ndSliced :=
  loopElimSlice piUp tgtM { cfg := .stmts ndUnitM' envEmpty, oracle := [int 2, int 7] }
#guard summary ⟨ndSliced.slices, ndSliced.claim⟩ ==
  ([some ndUnitM'], some (none, replayFuelGuess, [int 7]))
#guard match ndSliced.claim with
  | some (c, f) => enforcedGenuineAt tgtM piUp c f
  | none => false
#guard (mLink.lift ndUnitM ⟨ndSliced.slices, ndSliced.claim⟩).chain.isEmpty
#guard (mLink.lift ndUnitM ⟨[], some ({ cfg := .stmts ndUnitM' envEmpty, oracle := [int 7] },
  replayFuelGuess)⟩).chain.isEmpty

-- The real `loopElim` back-link, from the loop-free program: with a deterministic measure
-- snapshot its chain replay closes every gap, leaving a lone claim, which the certificate
-- translates to a genuine claim at the top of the input unit.
private def mFree : List Statement :=
  match Core.Transform.run (procOf mUnit') loopElim with
  | .ok (_, p) => bodyOf p
  | .error _ => []
private def mLoopElimOut : BackLinkOutcome Expression Command :=
  (loopElimBackLink piUp tgtM (loopOriginsStmts mUnit' mFree)).lift mUnit'
    ⟨[], some ({ cfg := .stmts mFree envEmpty, oracle := [int 2] }, replayFuelGuess)⟩
#guard summary mLoopElimOut == ([], some (some mUnit', replayFuelGuess, []))
#guard summary (mLink.lift mUnit mLoopElimOut) == ([], some (some mUnit, replayFuelGuess, []))
#guard match (mLink.lift mUnit mLoopElimOut).claim with
  | some (c, f) => enforcedGenuineAt tgtM piUp c f
  | none => false

/-! #### `precondElim` (a call to a function with a precondition)

`z := Int.SafeDiv(7, 1); assert tgt4 (z == 3)`; the phase inserts the division-by-zero
check before the `init`. -/

private def zVar : Expression.Expr := .fvar default (id "z") (some .int)
private def peUnit : List Statement :=
  [ .cmd (.cmd (.init (id "z") intTy
      (.det (.app default (.app default Core.intSafeDivOp (int 7)) (int 1))) md)),
    .cmd (.cmd (.assert "tgt4" (.eq default zVar (int 3)) md)) ]
private def tgt4 : AssertId Expression := { label := "tgt4", md := md }

private def peUnit' : List Statement :=
  match Core.Transform.run (procOf peUnit) Core.PrecondElim.precondElim
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .ok (_, p) => bodyOf p
  | .error _ => []

#guard peUnit'.length == 3
#guard insListB precondElimExt peUnit' peUnit

/-! `precondElimExt` takes the labels `precondElim` generates, and not a user label that only
contains `_calls_`. -/

#guard (peUnit'.filter fun
    | .cmd (.cmd (.assert l _ _)) => precondElimExt l
    | _ => false).length == 1
#guard !precondElimExt "no_calls_made"
#guard !precondElimExt "tgt_calls_f_"
#guard !precondElimExt "tgt4"

private def peLink :=
  exactBackLink "precondElim" (insCert precondElimExt piUp piUp (fun st => some st))
private def peTop : CexA Expression Command := { cfg := .stmts peUnit' envEmpty, oracle := [] }
private def peOut : BackLinkOutcome Expression Command := ⟨[], some (peTop, replayFuelGuess)⟩

#guard enforcedGenuineAt tgt4 piUp peTop replayFuelGuess
#guard summary (peLink.lift peUnit peOut) == ([], some (some peUnit, replayFuelGuess, []))
#guard match (peLink.lift peUnit peOut).claim with
  | some (c, f) => isTopLevelAtB peUnit c.cfg && enforcedGenuineAt tgt4 piUp c f
  | none => false

/-! ### Unchanged units (`ExactCert.ofUnchangedUnit`)

A phase that left the unit unchanged: the chain is kept as it is (no replay) and the
claim replays upstream; for a unit the phase rewrote the head has no counterpart. -/

private def ucLink := exactBackLink "unchanged"
  (ExactCert.ofUnchangedUnit (π' := piUp) (π := piUp) (isReplaySimulation_of_sub fun _ _ h => h)
    (fun st => some st))

#guard summary (ucLink.lift unit outTop) == ([], some (some unit, replayFuelGuess, []))
#guard summary (ucLink.lift unit outGaps) ==
  ([some unit, some [callStmt]], some (some [assertTgt], replayFuelGuess, []))
#guard match (ucLink.lift unit outGaps).claim with
  | some (c, f) => !isTopLevelAtB unit c.cfg && enforcedGenuine piUp c f
  | none => false
-- The rewritten `nondetElim` unit: the head starts at the downstream unit, not the input one.
#guard (ucLink.lift ndUnit ndOutTop).chain.isEmpty

end ExactBackLinkTest

end -- meta section
