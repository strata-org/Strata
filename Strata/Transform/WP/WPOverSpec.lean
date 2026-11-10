/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WP
public import Strata.Transform.Passive.Lang
public import Strata.Transform.Passive.Shadow
public import Strata.Transform.WP.WPOverWalk
public import Strata.Transform.Passive.WellTyped

/-! # The simulation property of the WP walk

The WP walk (`wpList`, `wpStmt`) is backward: it processes the rest of a list before its head,
so the walk state it is called with describes the point after a fragment and the state it
returns describes the point before it.  The simulation runs forward: from the loop-free store
`σ` and the guarded store `σL` related at the point before a fragment (by the state the walk of
the fragment returns), a loop-free run of the fragment gives a run of its guarded output whose
end is related at the point after it (by the state the walk was called with).

* `OnInv`: the relation on the loop-free path (the reach context holds in `σL`): every
  loop-free variable in scope that the continuation reads has its value in `σL` under its
  current WP name when that name is live, a value of the same declared types otherwise; the
  guarded store binds no name the rest of the guarded program declares.
* `OffInv`: the relation off the loop-free path (the reach context is false in `σL`).

Key definitions: `OnInv`, `OffInv`, `RunPost`, `OffPost`, `Spec`, `ListSpec`, `StmtSpec`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasSubstFvar P] [HasIdent P] [LawfulHasIdent P] [Hashable P.Ident] [HasFvars P]
  [WPLang P] [iIL : WPIteLang P] [HasOps P] [LawfulHasFvar P] [LawfulHasFvars P] [LawfulHasVal P]
omit iIL


/-- The guarded store binds no name that the guarded program emitted after the point with walk
    state `st` declares: a loop-free local it binds (not a non-avoided name of the form of a
    fresh name) is not declared later (`taken`), and a fresh
    name it binds that is not avoided has a counter from `st.next` on, or is the current WP name
    of a loop-free variable declared before the point, or is excepted (`Ex`: names an enclosing
    construct drew before walking the fragment and declared before it). -/
@[expose] def FreshInv (Lc : List P.Ident) (Ex : P.Ident → Prop) (st : WSt P)
    (σL : SemanticStore P) : Prop :=
  ∀ y, (σL y).isSome →
    (y ∈ Lc → (∀ b j, y = freshName b j → st.avoid.contains y = true) →
      st.taken.contains y = false) ∧
    ∀ b j, y = freshName b j → st.avoid.contains y = false →
      st.next ≤ j ∨ (∃ x : P.Ident, st.nm[x]? = some y) ∨ Ex y

/-- The facts of `OnInv` other than the reach condition: the relation between the loop-free
    store `σ` and the guarded store `σL` at a point with walk state `st`, scope `S`, and `V`
    variables read later. -/
structure OnCore (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (Lc : List P.Ident) (Ex : P.Ident → Prop) (st : WSt P)
    (S V : List P.Ident) (σ σL : SemanticStore P) : Prop where
  /-- A variable in scope read later has its value under its current live WP name. -/
  agree : ∀ x ∈ S, x ∈ V → ∀ n, curName st x = some n → st.live.contains n = true →
    σL n = σ x
  /-- A variable in scope read later is defined in both stores. -/
  defd : ∀ x ∈ S, x ∈ V → (σ x).isSome ∧ ∀ n, curName st x = some n → (σL n).isSome
  /-- The guarded value of a variable in scope whose current WP name has no final declared type
      has every type of its loop-free value. -/
  alike : ∀ x ∈ S, x ∈ V → ∀ n, curName st x = some n → (∀ ty, tyOfName T Y n ≠ .ok ty) →
    ∀ w w', σ x = some w → σL n = some w' → ∀ ty, HasVal.valueOfTy F w ty →
      HasVal.valueOfTy F w' ty
  /-- Locals out of scope are undefined in the loop-free store. -/
  undef : ∀ x ∈ Lc, x ∉ S → σ x = none
  canon : WellFormedStore σ F
  canonL : WellFormedStore σL F
  /-- Every guarded value of a name with a declared type of its own (not a copy or havoc name,
      whose type is that of another name) has the final declared type of its name. -/
  gtyped : ∀ n w, σL n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
    HasVal.valueOfTy F w ty
  /-- Every loop-free value of a variable in scope has the final declared type of its current
      WP name. -/
  ltyped : ∀ x ∈ S, x ∈ V → ∀ n, curName st x = some n → ∀ w, σ x = some w → ∀ ty,
    tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty
  fresh : FreshInv Lc Ex st σL

/-- The relation between the loop-free store `σ` and the guarded store `σL` at a point of the
    loop-free path with walk state `st`, reach context `κ`, scope `S`, and `V` the variables
    the loop-free continuation reads: `OnCore` and the reach context holds. -/
structure OnInv (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (Lc : List P.Ident) (Ex : P.Ident → Prop) (st : WSt P)
    (κ : RE P) (S V : List P.Ident) (σ σL : SemanticStore P) : Prop
    extends OnCore F T Y Lc Ex st S V σ σL where
  reach : κ.Holds F σL

/-- The guarded store at a point off the loop-free path with walk state `st`, reach context `κ`,
    scope `S` and `V` the variables read later: the reach context is false and its variables hold
    Booleans, the current WP names of the variables in scope read later are bound to values of
    their declared types, the store holds values of their final declared types, and binds no
    name the rest declares. -/
structure OffInv (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (Lc : List P.Ident) (Ex : P.Ident → Prop) (st : WSt P)
    (κ : RE P) (S V : List P.Ident) (σL : SemanticStore P) : Prop where
  canonL : WellFormedStore σL F
  reach : κ.Fails F σL
  /-- The variables of the reach context hold Booleans. -/
  bools : ∀ y ∈ RE.vars κ, σL y = some (HasBool.ttVal F) ∨ σL y = some (HasBool.ffVal F)
  /-- The current WP name of a variable in scope read later is bound, to a value of its final
      declared type. -/
  defd : ∀ x ∈ S, x ∈ V → ∀ n, curName st x = some n → ∃ w, σL n = some w ∧
    ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty
  gtyped : ∀ n w, σL n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
    HasVal.valueOfTy F w ty
  fresh : FreshInv Lc Ex st σL

/-- The exit snapshots a walk result `r` registered (walk output state `st'`), except `ex`, are
    false in `σL`. -/
@[expose] def SnapFF (F : P.Factory) (r : WRes P) (st' : WSt P) (ex : Option P.Ident)
    (σL : SemanticStore P) :
    Prop := ∀ l e, e ∈ r.regs.toList → e ∈ st'.pending.getD l [] → some e ≠ ex →
      σL e = some (HasBool.ffVal F)

/-- The exits of a fragment to labels other than `ex` for which it registered a snapshot have
    shadow ends satisfying `K`. -/
@[expose] def ExitEnds (r : WRes P) (st' : WSt P) (ex : Option String) (K : Outcome P → Prop) :
    Prop :=
  ∀ l e, e ∈ r.regs.toList → e ∈ st'.pending.getD l [] → some l ≠ ex → ∃ σs, K (.exit l σs)

/-- The shadow ends of a fragment satisfy `K`: its normal end when it does not always exit, and
    an exit to each label other than `ex` for which it registered a snapshot. -/
@[expose] def ShEnds (r : WRes P) (st' : WSt P) (ex : Option String) (K : Outcome P → Prop) :
    Prop := (r.ax = false → ∃ σs, K (.normal σs)) ∧ ExitEnds r st' ex K

/-- The selector of a carried merge `ite(e, var xB, var x)` evaluates to `b`. -/
@[expose] def SelIs (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (σL : SemanticStore P) (v : WExpr P) (b : Bool) : Prop :=
  ∃ e xB x, v = .ite e (.var xB) (.var x) ∧
    ∃ e', resolveE T Y e = .ok e' ∧
      P.eval F σL e' = some (if b then HasBool.ttVal F else HasBool.ffVal F)

omit [LawfulBEq P.Ident] [HasIdent P] [LawfulHasIdent P] [HasOps P] [LawfulHasFvar P]
    [LawfulHasFvars P] [LawfulHasVal P] in
/-- A selector evaluates to at most one Boolean. -/
theorem SelIs.ne {F : P.Factory} {T : Std.HashMap P.Ident P.Ty}
    {Y : Std.HashMap P.Ident P.Ident} {σL : SemanticStore P} {v : WExpr P}
    (h1 : SelIs F T Y σL v true) (h2 : SelIs F T Y σL v false) : False := by
  grind [SelIs, HasBool.tt_is_not_ff, HasBool.ttVal_ne_ffVal]

/-- The `i`-th carried merge at block depth `k` in the walk output state `st'` is
    `(n, v, xB)` and was registered by the walk result `r` (its copy `xB` is a registration). -/
@[expose] def CarryReg (r : WRes P) (st' : WSt P) (k i : Nat) (n : P.Ident) (v : WExpr P)
    (xB : P.Ident) : Prop := (st'.carries.getD k [])[i]? = some (n, v, xB) ∧ xB ∈ r.regs.toList

/-- Every carried merge a walk result `r` registered has a selector evaluating to `false`. -/
@[expose] def CarryFF (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (r : WRes P) (st' : WSt P) (σL : SemanticStore P) :
    Prop := ∀ k i n v xB, CarryReg r st' k i n v xB → SelIs F T Y σL v false

/-- Every carried merge `(n, v, xB)` a walk result `r` registered has a Boolean selector, a target
    `n` with a final declared type, and both its target and its copy bound to values of that
    type. -/
@[expose] def CarryOK (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (r : WRes P) (st' : WSt P) (σL : SemanticStore P) :
    Prop :=
  ∀ k i n v xB, CarryReg r st' k i n v xB →
    (SelIs F T Y σL v true ∨ SelIs F T Y σL v false) ∧ (∃ ty, tyOfName T Y n = .ok ty) ∧
    (∃ w, σL n = some w ∧ ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty) ∧
    ∃ w, σL xB = some w ∧ ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty

/-- The value `w` reaches the name `n` at the end of the block at depth `t`, through the carried
    merges a walk result `r` registered at depths from `t` on: no such merge of `n` selects and
    `n` holds `w`, or the selecting merge applied last (the shallowest block end, then the last
    in list order) has a copy holding `w`.  Every merge of `r` selects or not. -/
@[expose] def CarryAgree (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (r : WRes P) (st' : WSt P) (t : Nat)
    (σL : SemanticStore P) (n : P.Ident) (w : P.Val) : Prop :=
  (∀ k i v xB, CarryReg r st' k i n v xB → SelIs F T Y σL v true ∨ SelIs F T Y σL v false) ∧
  (((∀ k i v xB, t ≤ k → CarryReg r st' k i n v xB → SelIs F T Y σL v false) ∧
      σL n = some w) ∨
    ∃ k i v xB, t ≤ k ∧ CarryReg r st' k i n v xB ∧ SelIs F T Y σL v true ∧ σL xB = some w ∧
      ∀ k' i' v' xB', t ≤ k' → CarryReg r st' k' i' n v' xB' → SelIs F T Y σL v' true →
        k < k' ∨ (k = k' ∧ i' ≤ i))

/-- The name `n` was live, at walk state `st`, before each enclosing block at a depth from `t`
    on was entered: its live stamp is below the entry stamp of each such block. -/
@[expose] def LiveFrom (st : WSt P) (t : Nat) (n : P.Ident) : Prop :=
  ∀ (l : String) (j : Nat), st.labelDepth[l]? = some j → t ≤ j →
    liveBefore st n (st.stampAt.getD j 0) = true

/-- The relation at an exit of the loop-free path to the block at depth `t` with walk state `st`
    after the fragment (walk output `st'`, result `r`): `OnCore` with the agreement, through the
    carried merges the fragment registered (`CarryAgree`), of the names live after the enclosing
    blocks from depth `t` on (`LiveFrom`). -/
structure ExitCore (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (Lc : List P.Ident) (Ex : P.Ident → Prop) (st st' : WSt P)
    (r : WRes P) (t : Nat) (S V : List P.Ident) (σ σL : SemanticStore P) : Prop where
  xagree : ∀ x ∈ S, x ∈ V → ∀ n, curName st x = some n → st.live.contains n = true →
    LiveFrom st t n → ∀ w, σ x = some w → CarryAgree F T Y r st' t σL n w
  defd : ∀ x ∈ S, x ∈ V → (σ x).isSome ∧ ∀ n, curName st x = some n → (σL n).isSome
  alike : ∀ x ∈ S, x ∈ V → ∀ n, curName st x = some n → (∀ ty, tyOfName T Y n ≠ .ok ty) →
    ∀ w w', σ x = some w → σL n = some w' → ∀ ty, HasVal.valueOfTy F w ty →
      HasVal.valueOfTy F w' ty
  undef : ∀ x ∈ Lc, x ∉ S → σ x = none
  canon : WellFormedStore σ F
  canonL : WellFormedStore σL F
  gtyped : ∀ n w, σL n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
    HasVal.valueOfTy F w ty
  ltyped : ∀ x ∈ S, x ∈ V → ∀ n, curName st x = some n → ∀ w, σ x = some w → ∀ ty,
    tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty
  fresh : FreshInv Lc Ex st σL

/-- What a run of the guarded output of a fragment under a reach context `κ` establishes at its
    end, for the loop-free outcome `o` of the fragment (walk from `st` to `st'` with result `r`):
    * at every end, the fragment's carried merges well formed (`CarryOK`);
    * at a normal end, `OnInv` at the point after the fragment, the fragment's snapshots and
      carried merges false, the fragment neither always exiting nor ending its main list, and
      its untaken exits' shadow ends satisfying `X`;
    * at an exit to `l` (under a variable context), the guarded store off the path (`OffInv`,
      for the scope `S` before the fragment) with the untaken shadow ends to other labels
      satisfying `X`, the enclosing context `q` of a context `q ∧ ¬g` still true, and: when
      `l` labels an enclosing block of the region (at depth `t`), a snapshot the fragment
      registered for `l` true, the others false, the relation `ExitCore` for the variables
      `Lab l` read after the block (agreement through the fragment's carried merges), and the
      fragment's carried merges at depths below `t` false; when it does not, the fragment's
      snapshots false (the rest of the region is then off the path, and the carried merges
      only need to be well formed). -/
@[expose] def RunPost (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (Lc : List P.Ident) (Ex : P.Ident → Prop)
    (Lab : String → List P.Ident) (st st' : WSt P) (r : WRes P) (κ : RE P)
    (S S1 V1 : List P.Ident) (X : Outcome P → Prop) (σL' : SemanticStore P) : Outcome P → Prop
  | .normal σ1 => OnInv F T Y Lc Ex st κ S1 V1 σ1 σL' ∧ SnapFF F r st' none σL' ∧
      CarryFF F T Y r st' σL' ∧ CarryOK F T Y r st' σL' ∧ r.ax = false ∧ r.drop = false ∧
      ExitEnds r st' none X
  | .exit l σ1 => OffInv F T Y Lc Ex st κ S V1 σL' ∧ ShEnds r st' (some l) X ∧
      (∀ q g, κ = .andNeg q g → σL' q = some (HasBool.ttVal F)) ∧ CarryOK F T Y r st' σL' ∧
      match st.labelDepth[l]? with
      | some t => ∃ e, e ∈ r.regs.toList ∧ e ∈ st'.pending.getD l [] ∧
          σL' e = some (HasBool.ttVal F) ∧
          SnapFF F r st' (some e) σL' ∧ ExitCore F T Y Lc Ex st st' r t S1 (Lab l) σ1 σL' ∧
          ∀ k i n v xB, k < t → CarryReg r st' k i n v xB → SelIs F T Y σL' v false
      | none => SnapFF F r st' none σL'

/-- The final type maps `T`, `Y` (those the output is resolved with) extend the type maps of the
    walk state `st`, except for the types of names the rest of the walk may still declare: a
    loop-free local not yet declared (`taken`) and a fresh name not yet drawn (a counter from
    `st.next` on, not avoided); a name with a final type reference is one of `st` or not yet
    drawn. -/
@[expose] def FinalOK (Lc : List P.Ident) (st : WSt P) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) : Prop :=
  (∀ (n : P.Ident) ty, st.tys[n]? = some ty → T[n]? = some ty ∨
    (n ∈ Lc ∧ (∀ b j, n = freshName b j → st.avoid.contains n = true) ∧
      st.taken.contains n = false) ∨
    ∃ b j, n = freshName b j ∧ st.next ≤ j ∧ st.avoid.contains n = false) ∧
  (∀ (n x : P.Ident), st.tyOf[n]? = some x → Y[n]? = some x) ∧
  ∀ n : P.Ident, (Y[n]?).isSome → (st.tyOf[n]?).isSome ∨
    ∃ b j, n = freshName b j ∧ st.next ≤ j ∧ st.avoid.contains n = false

/-- The guarded store changes only the variables of the reach context `κ` among the names it
    binds. -/
@[expose] def Frame (κ : RE P) (σL σL' : SemanticStore P) : Prop :=
  ∀ y, (σL y).isSome → y ∉ RE.vars κ → σL' y = σL y

/-- What the walk of a fragment with result `r` (from `st` to `st'`, output resolved to `items`)
    guarantees for a failure of the fragment on the loop-free path at an event of kind `k` whose
    condition is `e`: the output has an obligation, the skeleton a slot for the target's label,
    and the resolved output a hit of the target at an event of kind `k` whose condition is `e`
    renamed by the WP names of `st'`. -/
@[expose] def HitPost (F : P.Factory) (st' : WSt P) (r : WRes P) (items : List (Item P))
    (σL : SemanticStore P) (t : AssertId P) (e : P.Expr) (k : Bool) : Prop :=
  r.hasObl = true ∧ SkObl t.label r.sk ∧
    ∃ wsub : List (P.Ident × P.Ident × Option P.Ty),
      (∀ q ∈ wsub, st'.back[q.2.1]? = some q.1 ∧ q.1 ∈ exprFV e) ∧
      ∃ tr, HitIn F items σL tr ∧ ClaimK k t (substObl wsub e) tr

/-- The off-path guarantee of the walk of a fragment (from `st` to `st'`, result `r`, resolved
    output `items`), from a guarded store `σL` off the path whose shadow run ends satisfy `K`:
    the output runs feasibly, the end is off the path (`OffInv` for the scope `S1` after the
    fragment, or `S` before it when the fragment always exits), only the context's variables
    change,
    the fragment's snapshots and carried merges are false, and its shadow ends satisfy `K`. -/
@[expose] def OffPost (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (Lc : List P.Ident) (Ex : P.Ident → Prop) (st st' : WSt P)
    (r : WRes P) (κ : RE P) (S S1 V1 : List P.Ident) (items : List (Item P))
    (σL : SemanticStore P) (K : Outcome P → Prop) : Prop :=
  ∃ tr σL', MainRun F items σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
    OffInv F T Y Lc Ex st κ (if r.ax then S else S1) V1 σL' ∧
    Frame κ σL σL' ∧ SnapFF F r st' none σL' ∧ CarryFF F T Y r st' σL' ∧
    CarryOK F T Y r st' σL' ∧ ShEnds r st' none K

/-- The names declared by the `init`s nested in the blocks and `ite`s of a list (not at its top
    level). -/
@[expose] def nestedInits (ss : PStmts P) : List P.Ident :=
  ss.flatMap fun s => match s with
    | .cmd _ => []
    | s => stmtsInits [s]

/-- The typing `Γ` of the scope `S` agrees with the final type maps `T`, `Y` at the walk state
    `st`: the current WP name of every variable of `S` that `Γ` types has that type. -/
@[expose] def TyCtx (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) (st : WSt P)
    (S : List P.Ident) (Γ : VarTyping P) : Prop :=
  ∀ x ∈ S, ∀ ty, Γ x = some ty → ∀ n, curName st x = some n → tyOfName T Y n = .ok ty

omit [LawfulHasIdent P] [HasOps P] [LawfulHasFvar P] [LawfulHasFvars P]
    [LawfulHasVal P] in
/-- The agreement of a typing at a walk state carries to a state whose current names of the
    variables of the scope are current names at the first. -/
theorem TyCtx.back {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident} {st st' : WSt P}
    {S : List P.Ident} {Γ : VarTyping P} (h : TyCtx T Y st' S Γ)
    (hc : ∀ x ∈ S, ∀ n, curName st x = some n → curName st' x = some n) : TyCtx T Y st S Γ :=
  fun x hx ty hty n hn => h x hx ty hty n (hc x hx n hn)

/-- The expressions of the fragment `ss` are typed under the typing predicate of `tE` and the
    typing `Γ` of the names in scope before it, and its annotations agree with `Γ`. -/
@[expose] def ExprsTyped (tE : TypedEval P) (Γ : VarTyping P) (ss : PStmts P) : Prop :=
  Block.ExprsTyped tE.Typ Γ ss

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasSubstFvar P] [HasIdent P]
    [LawfulHasIdent P] [Hashable P.Ident] [WPLang P] [HasOps P] [LawfulHasFvar P]
    [LawfulHasFvars P] [LawfulHasVal P] in
/-- The expressions of a statement followed by a list are typed: those of the statement under
    `Γ`, and those of the list under `Γ` extended with the statement's definitions. -/
theorem ExprsTyped.cons {tE : TypedEval P} {Γ : VarTyping P} {s : PStmt P} {rest : PStmts P}
    (h : ExprsTyped tE Γ (s :: rest)) :
    ExprsTyped tE Γ [s] ∧ ExprsTyped tE (Γ.extend (Stmt.typedDefinedVars s)) rest := by
  simp only [ExprsTyped, Block.ExprsTyped, Block.rhsTyped, Block.condsTyped,
    Block.fvarTypesWellAnnotated,
    and_true] at h ⊢
  exact ⟨⟨h.1.1, h.2.1.1, h.2.2.1⟩, h.1.2, h.2.1.2, h.2.2.2⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasSubstFvar P] [HasIdent P]
    [LawfulHasIdent P] [Hashable P.Ident] [WPLang P] [HasOps P] [LawfulHasFvar P]
    [LawfulHasFvars P] [LawfulHasVal P] in
/-- The expressions of a block's body are typed when those of the block are. -/
theorem ExprsTyped.block {tE : TypedEval P} {Γ : VarTyping P} {l : String} {body : PStmts P}
    {md : MetaData P} (h : ExprsTyped tE Γ [.block l body md]) : ExprsTyped tE Γ body := by
  simp only [ExprsTyped, Block.ExprsTyped, Block.rhsTyped, Block.condsTyped,
    Block.fvarTypesWellAnnotated,
    Stmt.rhsTyped, Stmt.condsTyped, Stmt.fvarTypesWellAnnotated, and_true] at h
  exact h

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasSubstFvar P] [HasIdent P]
    [LawfulHasIdent P] [Hashable P.Ident] [WPLang P] [HasOps P] [LawfulHasFvar P]
    [LawfulHasFvars P] [LawfulHasVal P] in
/-- The expressions of a deterministic `ite` are typed: its condition is Boolean, its annotations
    agree with `Γ`, and the expressions of its arms are typed. -/
theorem ExprsTyped.ite {tE : TypedEval P} {Γ : VarTyping P} {c : P.Expr} {tss ess : PStmts P}
    {md : MetaData P} (h : ExprsTyped tE Γ [.ite (.det c) tss ess md]) :
    tE.Typ c HasBool.boolTy ∧ Γ.annotates (HasFvars.getTypedFvars c) ∧ ExprsTyped tE Γ tss ∧
      ExprsTyped tE Γ ess := by
  simp only [ExprsTyped, Block.ExprsTyped, Block.rhsTyped, Block.condsTyped,
    Block.fvarTypesWellAnnotated,
    Stmt.rhsTyped, Stmt.condsTyped, Stmt.fvarTypesWellAnnotated, and_true] at h
  exact ⟨h.1.1, h.2.2.1, ⟨h.1.2.1, h.2.1.1, h.2.2.2.1⟩, h.1.2.2, h.2.1.2, h.2.2.2.2⟩

/-- The typing after a statement: every walk of `s` after which an obligation follows (from `st`
    to `st'`) under final type maps
    `T`, `Y` extending `st'`, of a statement well scoped from `S` whose names of the form of a fresh
    name are avoided, carries the agreement of a typing `Γ` of `S` at `st'` (before `s`) to the
    agreement of `Γ` extended with the definitions of `s`, of the scope after `s`, at `st`. -/
@[expose] def StmtTyCtx (Lc : List P.Ident) (κ : RE P) (d : Nat) (s : PStmt P) : Prop :=
  ∀ st r st', WFSt st → (wpStmt κ d true s).run st = .ok (r, st') →
  ∀ T Y, FinalOK Lc st' T Y → ∀ S, Stmt.WellScoped Lc S s →
  (∀ x ∈ S ++ Block.idents [s], ∀ b j, x = freshName b j → st.avoid.contains x = true) →
  ∀ Γ, TyCtx T Y st' S Γ → TyCtx T Y st (Stmt.topInits s ++ S) (Γ.extend (Stmt.typedDefinedVars s))

/-- The simulation property of the walk `m` of a fragment `ss` (a list, or the one statement of a
    statement walk) with reach context `κ`, for the loop-free locals `Lc`; `hitP`, `runP`, `offP`
    are the fragment's annotated reaches, annotated runs and shadow runs.  For every walk from
    `st` (well formed) to `st'` with result `r` whose output is resolved to `items` under final
    maps `T`, `Y` extending `st'`, every scope `S` from which the fragment is well scoped
    (`wf S`), every typing `Γ` of `S` under which the expressions of the fragment are typed
    (`ExprsTyped`) and which agrees with `T`, `Y` at `st'` (`TyCtx`) when an obligation follows
    the fragment or the fragment has one, every scope `S` whose names and those of the fragment
    of the form of a fresh name are avoided,
    every set `Ex` of excepted names (fresh names with counters below `st.next` that are not
    renamings), every continuation `k`, every label map `Lab` giving, for each label of an
    enclosing block of the region (at a depth at most `d`), variables of `S` the continuation
    reads, and a context `κ` whose variables are fresh names drawn before the walk (counters
    below `st.next`, not avoided, not renamings in `st` and without back entry), from a state
    whose discarded registrations were drawn before (`DeadBelow`), whose live names are avoided
    or drawn before (`LiveKeys`), and with no carried merges below the depth `d`:
    * a failure of the fragment on the loop-free path (`OnInv` before it) is a hit of the output
      at an event of the same kind and id (`HitPost`);
    * when an obligation follows (`fol`), a feasible loop-free run of the fragment is a feasible
      run of the output establishing `RunPost` at its end, except for an exit under `top`
      (which ends the main list: nothing of the guarded program after it is on the path);
    * when an obligation follows, off the path (`OffInv` before it), a shadow run of the
      fragment gives a run of the output (`OffPost`). -/
@[expose] def Spec (F : P.Factory) (tE : TypedEval P) (Lc : List P.Ident) (κ : RE P) (d : Nat)
    (m : WM P (WRes P))
    (ss : PStmts P) (wf : List P.Ident → Prop) (fol : Bool)
    (hitP : SemanticStore P → List (Event P) → Prop)
    (runP : (Outcome P → Prop) → SemanticStore P → List (Event P) → Outcome P → Prop)
    (offP : SemanticStore P → (Outcome P → Prop) → Prop) : Prop :=
  ∀ st r st', WFSt st → m.run st = .ok (r, st') →
  ∀ T Y, FinalOK Lc st' T Y → ∀ items, resolveItems T Y r.out.toList = .ok items →
  ∀ S, wf S → ∀ Γ, (fol = true ∨ r.hasObl = true → TyCtx T Y st' S Γ) → ExprsTyped tE Γ ss →
  (∀ x ∈ S ++ Block.idents ss, ∀ b j, x = freshName b j → st.avoid.contains x = true) →
  ∀ Ex : P.Ident → Prop,
    (∀ y, Ex y → (∀ b j, y = freshName b j → j < st.next) ∧ st'.back[y]? = none) →
  ∀ (k : List (PStmts P)) (Lab : String → List P.Ident),
    (∀ l t, st.labelDepth[l]? = some t → t ≤ d ∧ ∀ x ∈ Lab l, x ∈ contFV k ∧ x ∈ S) →
    (∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st.next) ∧ st.avoid.contains y = false ∧
      (∀ x : P.Ident, st.nm[x]? ≠ some y) ∧ st.back[y]? = none) →
    DeadBelow st → LiveKeys st → (∀ k, d < k → st.carries.getD k [] = []) →
    (∀ σ σL t e b tr, OnInv F T Y Lc Ex st' κ S (contFV (ss :: k)) σ σL → hitP σ tr →
      ClaimK b t e tr → HitPost F st' r items σL t e b) ∧
    (fol = true → ∀ σ σL X evs o, OnInv F T Y Lc Ex st' κ S (contFV (ss :: k)) σ σL →
      runP X σ evs o → Trace.AssumptionsHold P evalInterp () evs →
      (κ = .top ∧ ∃ l σ1, o = .exit l σ1) ∨
      ∃ tr σL', MainRun F items σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
        RunPost F T Y Lc Ex Lab st st' r κ S (scopeAfter S ss) (contFV k) X σL' o) ∧
    (fol = true → ∀ σs σL K, OffInv F T Y Lc Ex st' κ S (contFV (ss :: k)) σL → offP σs K →
      OffPost F T Y Lc Ex st st' r κ S (scopeAfter S ss) (contFV k) items σL K)

/-- `Spec` of a statement list walk, for the walks that occur: under `top`, no obligation
    follows the list. -/
abbrev ListSpec (F : P.Factory) (tE : TypedEval P) (Lc : List P.Ident) (κ : RE P) (d : Nat)
    (fEnd : Bool)
    (ss : PStmts P) : Prop :=
  (κ = .top → fEnd = false) →
  Spec F tE Lc κ d (wpList κ d fEnd ss) ss (fun S => Block.WellScoped Lc S ss) fEnd (DReach F ss)
    (fun X => DRun F X ss) (ShL F ss)

/-- `Spec` of a statement walk. -/
abbrev StmtSpec (F : P.Factory) (tE : TypedEval P) (Lc : List P.Ident) (κ : RE P) (d : Nat)
    (f : Bool)
    (s : PStmt P) : Prop :=
  Spec F tE Lc κ d (wpStmt κ d f s) [s] (fun S => Stmt.WellScoped Lc S s) f (DReachS F s)
    (fun X => DRunS F X s) (ShS F s)

end -- public section

end WP
end Imperative
