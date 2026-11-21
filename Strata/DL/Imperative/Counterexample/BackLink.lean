/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Counterexample.Run

/-! # Back-links: level-(a) counterexamples across program transformations

A *back-link* translates a level-(a) counterexample (a run of the program, `CexA`) of a
transformation's output into one of its input.  This module holds the generic machinery,
in the pure-expression bundle and command language: the `BackLink` a transformation's
inverse is, the composition of back-links along a pipeline (`composeBackLinks`, and
`composeTargeted` for phases that rewrite the target), and the replay-free back-link of an
exact phase built from a simulation certificate (`ExactCert`, `exactBackLink`).

Key definitions: `BackLink`, `composeBackLinks`, `composeStep`, `TargetedBackLink`,
`composeTargeted`, `ExactCert`, `exactBackLink`.
-/

namespace Imperative

public section

universe u
variable {P : PureExpr.{u}} {CmdT : Type}

/-! ## Back-link procedures (specification and composition)

The generic machinery for chaining back-links: the `BackLink` specification a
transformation's inverse satisfies, and the generic `composeBackLinks` that
chains them.  A back-link maps the downstream `BackLinkOutcome` to its own.
This section uses only the counterexample structures of `Counterexample.Run`: it does not
run the replay (an individual back-link may), and the validation verdicts do not depend on
it.  It defines no transformation-specific back-link. -/

/-- Generic counterexample back-link: maps the downstream node's outcome to this
    node's outcome.  It is only the lift; the forward pass it inverts, and the
    obligation that `lift` preserves outcome validity across that pass, are supplied
    where the forward transformation is known, not stored here. -/
structure BackLink (P : PureExpr) (CmdIn CmdOut : Type)
    [HasBool P] [DecidableEq P.Expr] [InterpLang P] where
  name : String
  lift : List (Stmt P CmdIn) → BackLinkOutcome P CmdOut → BackLinkOutcome P CmdIn

/-- Apply back-links in reverse forward-execution order, threading the outcome.
    The empty chain is sticky: once composition reaches an outcome with no
    counterexample data to carry backward, it stays `BackLinkOutcome.empty` (a
    missing/dead-ending link cannot resurrect a witness for an earlier node).
    Composition does not inspect claims; whether a link claims its last slice by
    validation or by a one-time proof is internal to the link. -/
def composeBackLinks [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (links : List (BackLink P CmdT CmdT))
    (sts : List (List (Stmt P CmdT)))
    (initial : BackLinkOutcome P CmdT) :
    BackLinkOutcome P CmdT :=
  (links.zip sts).reverse.foldl (init := initial) fun outcome (link, st) =>
    match outcome with
    | ⟨[], none⟩ => .empty
    | _ => link.lift st outcome

/-- A back-link that lifts nothing at an empty unit: at run time a phase whose input has
    no unit for the obligation (e.g. a procedure the phase synthesized) is lifted at `[]`,
    and translating a chain there would carry configurations of a unit that does not
    exist upstream. -/
@[expose] def BackLink.guardEmptyUnit [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {CmdIn CmdOut : Type} (link : BackLink P CmdIn CmdOut) : BackLink P CmdIn CmdOut where
  name := link.name
  lift st o := if st.isEmpty then .empty else link.lift st o

/-- Use `fallback` where `primary` translates nothing of a non-empty chain (e.g. an
    exact back-link whose checker rejects the unit). -/
@[expose] def BackLink.orElseIfEmpty [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {CmdIn CmdOut : Type} (primary fallback : BackLink P CmdIn CmdOut) :
    BackLink P CmdIn CmdOut where
  name := primary.name
  lift st o :=
    let r := primary.lift st o
    if r.chain.isEmpty && !o.chain.isEmpty then fallback.lift st o else r

/-- Use `fallback`'s outcome where `primary` claims nothing and `fallback` does. -/
@[expose] def BackLink.preferClaim [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {CmdIn CmdOut : Type} (primary fallback : BackLink P CmdIn CmdOut) :
    BackLink P CmdIn CmdOut where
  name := primary.name
  lift st o :=
    let r := primary.lift st o
    if r.claim.isNone then
      let r' := fallback.lift st o
      if r'.claim.isSome then r' else r
    else r

/-- The sticky per-link fold step used by `composeBackLinks`: thread the outcome
    through one back-link, keeping the empty outcome sticky. -/
def composeStep [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (st : List (Stmt P CmdT)) :
    BackLinkOutcome P CmdT → BackLink P CmdT CmdT → BackLinkOutcome P CmdT :=
  fun outcome link => match outcome with | ⟨[], none⟩ => .empty | _ => link.lift st outcome

/-! ## Target-threading composition

A back-link lifts a counterexample for one *target* (the obligation being explained).
Most phases keep the target's identity, but a phase that synthesizes the obligation
(call elimination's precondition asserts, loop-invariant asserts) must rewrite it for
the phases upstream of it.  A `TargetedBackLink` pairs the deferred back-link builder
with that rewrite; the composition instantiates each link at the target *as rewritten
by the links downstream of it*.  The target type `Tgt` is a parameter, so a richer
target (e.g. a loop-VC id) reuses the same composition. -/

/-- A back-link builder keyed on the target it explains, with the map from the target
    at the phase's output to the target at its input (`id` for a phase that keeps
    obligation ids). -/
structure TargetedBackLink (P : PureExpr) (CmdT : Type) (Tgt : Type)
    [HasBool P] [DecidableEq P.Expr] [InterpLang P] where
  build : Tgt → BackLink P CmdT CmdT
  upstream : Tgt → Tgt := id

/-- The target at the input of the first of `links` (forward order), given the target
    `t` at the output of the last: each link's `upstream` applied from the last link
    back to the first. -/
def targetIn [HasBool P] [DecidableEq P.Expr] [InterpLang P] {Tgt : Type} :
    List (TargetedBackLink P CmdT Tgt) → Tgt → Tgt
  | [], t => t
  | l :: ls, t => l.upstream (targetIn ls t)

/-- Reverse composition with target threading: the first link (forward order) is
    applied last, at its own input unit, built at the target at its input
    (`targetIn`).  The empty outcome is sticky (`composeStep`). -/
def composeTargeted [HasBool P] [DecidableEq P.Expr] [InterpLang P] {Tgt : Type} :
    List (TargetedBackLink P CmdT Tgt) → List (List (Stmt P CmdT)) → Tgt →
      BackLinkOutcome P CmdT → BackLinkOutcome P CmdT
  | l :: ls, st :: sts, t, initial =>
    composeStep st (composeTargeted ls sts t initial) (l.build (targetIn (l :: ls) t))
  | _, _, _, initial => initial

/-! ## Replay-free back-links of exact phases

An *exact* phase loses no behaviour: every downstream execution has an upstream counterpart.
Its back-link translates the incoming outcome (every slice and the claim, with its fuel) with
no replay, and the translated outcome is valid by one proof (`exactBackLink_preserves` in
`Strata.DL.Imperative.Counterexample.BackLinkProps`) from a per-phase *simulation
certificate* (`ExactCert`).  The definitions are generic over the language, the target type
`Tgt`, the claim-validity predicate of each side and the well-formedness `WF` of a slice
start; the only place a target is transformed is the certificate field `backTarget`. -/

/-- **Simulation certificate of an exact phase.**  `T` is the phase's per-unit forward map
    (`T st = some st'`: the upstream unit `st` becomes the downstream unit `st'`); `V'`/`V`
    are the claim-validity predicates downstream/upstream; `WF` is the well-formedness of a
    slice start.  The maps receive the upstream unit `st`, so a phase can rebuild an upstream
    configuration from it (e.g. the top of the unit). -/
structure ExactCert [InterpLang P] (WF : IConfig P CmdT → Prop)
    (T : List (Stmt P CmdT) → Option (List (Stmt P CmdT)))
    {Tgt : Type} (V' V : CexValidity P CmdT Tgt) where
  /-- Map a downstream slice start back into the upstream unit `st` (`none`: no
      counterpart).  The flag says whether the slice heads the chain (the head starts at
      the top of the downstream unit; a later element need not). -/
  backCfg : List (Stmt P CmdT) → Bool → IConfig P CmdT → Option (IConfig P CmdT)
  /-- Map a downstream oracle (of a slice starting at the given configuration) to the
      upstream one. -/
  backOracle : List (Stmt P CmdT) → IConfig P CmdT → List P.Expr → List P.Expr
  /-- Map a downstream target to the upstream one (identity unless the phase renames). -/
  backTarget : Tgt → Tgt
  /-- Upstream fuel sufficient for a downstream claim fuel in the upstream unit `st`
      (interpreter steps and expression evaluation, one fuel).  It sees the unit so a phase
      can bound the upstream run statically by the unit's size. -/
  backFuel : List (Stmt P CmdT) → Nat → Nat
  /-- A slice that starts at the top of the downstream unit maps to one that starts at
      the top of the upstream unit. -/
  top_back : ∀ st st', T st = some st' → ∀ (c' : CexA P CmdT) c,
    isTopLevelAt st' c' → backCfg st true c'.cfg = some c →
    ∀ oracle, isTopLevelAt st ⟨c, oracle⟩
  /-- A slice that does not start at the top of the downstream unit maps to one that
      does not start at the top of the upstream unit. -/
  nontop_back : ∀ st st', T st = some st' → ∀ (c' : CexA P CmdT) c,
    ¬ isTopLevelAt st' c' → backCfg st false c'.cfg = some c →
    ∀ oracle, ¬ isTopLevelAt st ⟨c, oracle⟩
  /-- A well-formed downstream slice start maps to a well-formed upstream one. -/
  wf_back : ∀ st st', T st = some st' → ∀ (head : Bool) (c' c : IConfig P CmdT),
    WF c' → backCfg st head c' = some c → WF c
  /-- **Claim transport**: a valid (and well-formed) downstream claim, translated, is
      valid upstream. -/
  claim_back : ∀ st st', T st = some st' → ∀ (t : Tgt) (f : Nat) (head : Bool)
    (c' : CexA P CmdT) c, WF c'.cfg → V' t f c' → backCfg st head c'.cfg = some c →
    V (backTarget t) (backFuel st f) ⟨c, backOracle st c'.cfg c'.oracle⟩

namespace ExactCert

variable [InterpLang P] {WF : IConfig P CmdT → Prop}
  {T : List (Stmt P CmdT) → Option (List (Stmt P CmdT))} {Tgt : Type}
  {V' V : CexValidity P CmdT Tgt}

/-- Translate one downstream slice into the upstream unit `st`. -/
@[expose] def backCex (cert : ExactCert WF T V' V) (st : List (Stmt P CmdT))
    (head : Bool) (c' : CexA P CmdT) : Option (CexA P CmdT) :=
  (cert.backCfg st head c'.cfg).map fun c => ⟨c, cert.backOracle st c'.cfg c'.oracle⟩

/-- Translate a downstream outcome into the upstream unit `st`, with no replay.
    The head slice must have a counterpart (otherwise the outcome is empty); a later
    unconfirmed slice without counterpart is dropped; the claim is translated with its
    fuel mapped by `backFuel` (and dropped if it has no counterpart). -/
@[expose] def liftOutcome (cert : ExactCert WF T V' V) (st : List (Stmt P CmdT))
    (o : BackLinkOutcome P CmdT) : BackLinkOutcome P CmdT :=
  match o.slices with
  | [] =>
    match o.claim with
    | none => .empty
    | some (c', f) =>
      match cert.backCex st true c' with
      | none => .empty
      | some c => ⟨[], some (c, cert.backFuel st f)⟩
  | h' :: rest =>
    match cert.backCex st true h' with
    | none => .empty
    | some h =>
      ⟨h :: rest.filterMap (cert.backCex st false),
       o.claim.bind fun cf => (cert.backCex st false cf.1).map fun c => (c, cert.backFuel st cf.2)⟩

end ExactCert

/-- **The replay-free back-link of an exact phase.** -/
@[expose] def exactBackLink [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {WF : IConfig P CmdT → Prop} {T : List (Stmt P CmdT) → Option (List (Stmt P CmdT))}
    {Tgt : Type} {V' V : CexValidity P CmdT Tgt} (name : String) (cert : ExactCert WF T V' V) :
    BackLink P CmdT CmdT where
  name := name
  lift := cert.liftOutcome

end -- public section

end Imperative
