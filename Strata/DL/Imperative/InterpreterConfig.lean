/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterTypes
public import Strata.Util.ListMapProps

/-! # `IConfig`: the monadic interpreter's configuration type

The monadic interpreter (`stepInterp`/`runInterp`) steps over `IConfig`, which mirrors the
semantics' `Config` except at a block: an `IConfig` block carries a *scope frame* (`ScopeFrame`),
the parent store at block entry together with the list of names the block has defined. Exiting a
block the monadic interpreter opened drops exactly those names (`IStore.drop`), so the exit store is
the inner store without the block's names, never the parent store.

* `InterpLang`: the language data of the engine, among them the finite map in which the
  interpreter store keeps its entries, with its laws;
* `IStore`, `IEnv`: the monadic interpreter's store (a base store and the entries written over it)
  and environment;
* `CmdDefs`: the names a command may newly define, which the monadic interpreter adds to the frame
  of the enclosing block;
* `ScopeFrame`, `ScopeFrame.exit`, `ScopeFrame.record`: the frame, the exit store and the frame
  after a step;
* `IConfig`, `IConfig.abs F` (the semantic configuration an `IConfig` stands for under the
  factory `F`), `IConfig.Denoting`, `IConfig.Denotes` (an `IConfig` whose stores denote under
  `F`, and one that denotes a given semantic configuration);
* `ScopeFrame.Exact`, `IConfig.Tracked`: the frames list exactly the block-local names, so that
  the exit store is the semantic projection;
* `DefinesWithin`, `CmdDefsSound`: a command relation defines only the names `CmdDefs` lists.

Lemmas about these definitions are in `InterpreterConfigProps.lean`. -/

namespace Imperative

public section

variable {P : PureExpr} {CmdT : Type}

/-! ## Names a command may define -/

/-- The names a command may newly define in the store it runs on. -/
class CmdDefs (P : PureExpr) (CmdT : Type) where
  defs : CmdT → List P.Ident

/-- A base command may define only the binder of an `init`. -/
instance : CmdDefs P (Cmd P) where
  defs := Cmd.definedVars

/-- A base command may define the binder of an `init`, a call its left-hand sides. -/
instance : CmdDefs P (CmdExt P) where
  defs
    | .cmd c => c.definedVars
    | .call _ args _ => CallArg.getLhs args

/-- Every name `σ'` defines is defined in `σ` or listed in `L`. -/
@[expose] def DefinesWithin (σ σ' : SemanticStore P) (L : List P.Ident) : Prop :=
  ∀ x, (σ' x).isSome → (σ x).isSome ∨ x ∈ L

/-- Every evaluation of a command under `EvalCmd` defines only names in `CmdDefs.defs` beyond the
    names its input store defines. -/
@[expose] def CmdDefsSound [CmdDefs P CmdT] {EventT : Type _}
    (EvalCmd : EvalCmdParamE P CmdT EventT) : Prop :=
  ∀ f σ c σ' evs, EvalCmd f σ c σ' evs → DefinesWithin σ σ' (CmdDefs.defs (P := P) c)

/-! ## The language's interpreter data -/

/-- The **language-fixed** data the monadic interpreter needs, bundled as a
    P-only typeclass — distinct from the *per-run* knobs (`haltOn`/`oracleConfig`),
    which stay in the run config.  A language provides one instance; Core's
    has `ops := replayValueOps`, `boundedEval := Core.evalBounded` and keeps the
    interpreter store's entries in a `Std.TreeMap`.

    The engine runs on *runtime* data: runtime stores (`RStore P`, holding value expressions)
    and a runtime factory (`RFactory`).  The semantic configurations (`Config`, holding `P.Val`)
    are only reasoned about, through `denote`.

    * `RFactory`, `rfactory` — the computable factory the engine evaluates with, and the one of a
      semantic factory.
    * `ops` — the executable value predicates (`isValue`/`hasType`/`sameType`).
    * `boundedEval` — the fuel-bounded evaluator the engine applies to reduce a
      pure expression over a runtime store (never the unbounded `P.eval`).
    * `denote` — the semantic value a runtime value denotes under a factory (`InterpLang.Denotes`
      is its graph).
    * `eqModuloMeta` — equality of runtime values up to their metadata.
    * `Writes` and its operations — the finite map in which the interpreter store
      (`IStore`) keeps the entries written over its base store, with the laws of a
      function updated pointwise; the engine and its proofs use only these laws. -/
class InterpLang (P : PureExpr) where
  /-- The computable factory the engine evaluates with. -/
  RFactory : Type
  /-- The runtime factory of a semantic factory. -/
  rfactory : P.Factory → RFactory
  ops : ReplayValueOps P RFactory
  boundedEval : Nat → RFactory → RStore P → P.Expr → Option P.Expr
  /-- The semantic value a runtime value denotes under a factory, if any.  It is a partial
      function, whose graph is `InterpLang.Denotes`, so that a runtime configuration has one
      semantic image `IConfig.abs F`. -/
  denote : P.Factory → P.Expr → Option P.Val
  /-- The type of a value, when the language can read it off the value.  The
      engine uses it as the type source of a nondeterministic assignment
      `set x := *`: the fresh value is drawn at the type of `x`'s current value.
      `none` means the type is unknown, and the engine stops
      (`StopReason.unsupportedNondetSet`).  No law is required of it: the engine
      re-checks the drawn value with `ops.isValue`/`ops.sameType`, exactly as for
      a deterministic `set`. -/
  typeOf : RFactory → P.Expr → Option P.Ty
  /-- Equality of runtime values up to their metadata: the comparison by which the engine
      recognizes a runtime value as a given literal, so that the metadata a value carries does not
      decide which literal it is. -/
  eqModuloMeta : P.Expr → P.Expr → Bool
  /-- The finite maps from names to entries. -/
  Writes : Type
  /-- The map with no entries. -/
  writesEmpty : Writes
  /-- The entry of a name, if the map has one. -/
  writesFind? : Writes → P.Ident → Option (Option P.Expr)
  /-- The map with the entry of a name set, replacing its previous entry. -/
  writesInsert : Writes → P.Ident → Option P.Expr → Writes
  /-- The map without an entry for a name. -/
  writesErase : Writes → P.Ident → Writes
  /-- The empty map has no entries. -/
  writesFind?_empty : ∀ x, writesFind? writesEmpty x = none
  /-- A name's entry is the one last inserted for it. -/
  writesFind?_insert_self : ∀ w x e, writesFind? (writesInsert w x e) x = some e
  /-- Inserting an entry for one name leaves the entry of every other name. -/
  writesFind?_insert_ne : ∀ w x y e, y ≠ x → writesFind? (writesInsert w x e) y = writesFind? w y
  /-- An erased name has no entry. -/
  writesFind?_erase_self : ∀ w x, writesFind? (writesErase w x) x = none
  /-- Erasing one name leaves the entry of every other name. -/
  writesFind?_erase_ne : ∀ w x y, y ≠ x → writesFind? (writesErase w x) y = writesFind? w y

/-- The runtime value `r` denotes the semantic value `v` under the factory `F`. -/
@[expose] def InterpLang.Denotes [InterpLang P] (F : P.Factory) (r : P.Expr) (v : P.Val) : Prop :=
  InterpLang.denote F r = some v

/-- The Boolean literal a runtime value is, up to metadata (`InterpLang.eqModuloMeta`): `some true`
    for `HasBool.tt`, `some false` for `HasBool.ff`, `none` for any other value.  The engine
    recognizes guard values and assumption conditions through it. -/
@[expose] def InterpLang.boolLit? [HasBool P] [InterpLang P] (v : P.Expr) : Option Bool :=
  if InterpLang.eqModuloMeta v (HasBool.tt (P := P)) then some true
  else if InterpLang.eqModuloMeta v (HasBool.ff (P := P)) then some false
  else none

/-- The Boolean literals denote the Boolean values of every factory, and so does every runtime
    value equal to one of them up to metadata. -/
class InterpLangBool (P : PureExpr) [HasBool P] [InterpLang P] : Prop where
  denote_tt : ∀ F, InterpLang.Denotes F (HasBool.tt (P := P)) (HasBool.ttVal F)
  denote_ff : ∀ F, InterpLang.Denotes F (HasBool.ff (P := P)) (HasBool.ffVal F)
  /-- A runtime value equal to `tt` up to metadata denotes only `ttVal`. -/
  denote_of_eqModuloMeta_tt : ∀ F r v, InterpLang.eqModuloMeta r (HasBool.tt (P := P)) = true →
    InterpLang.Denotes F r v → v = HasBool.ttVal F
  /-- A runtime value equal to `ff` up to metadata denotes only `ffVal`. -/
  denote_of_eqModuloMeta_ff : ∀ F r v, InterpLang.eqModuloMeta r (HasBool.ff (P := P)) = true →
    InterpLang.Denotes F r v → v = HasBool.ffVal F

/-- The semantic store a runtime store stands for under the factory `F`: each value expression
    replaced by its denotation (a value with no denotation leaves the name undefined). -/
@[expose] def InterpLang.absStore [InterpLang P] (F : P.Factory) (σr : RStore P) :
    SemanticStore P :=
  fun x => (σr x).bind (InterpLang.denote F)

/-- Every value of the runtime store `σr` denotes a semantic value under `F`. -/
@[expose] def RStore.Denoting [InterpLang P] (F : P.Factory) (σr : RStore P) : Prop :=
  ∀ x r, σr x = some r → ∃ v, InterpLang.Denotes F r v

/-- The runtime store `σr` denotes the semantic store `σ` under `F`: the same names are
    defined, and each runtime value denotes the semantic value of its name. -/
@[expose] def StoreDenotes [InterpLang P] (F : P.Factory) (σr : RStore P) (σ : SemanticStore P) :
    Prop :=
  (∀ x, σ x = none ↔ σr x = none) ∧
    (∀ x r v, σr x = some r → σ x = some v → InterpLang.Denotes F r v)

/-- The default language data for a language whose factory is computable: the runtime
    factory is the factory itself, with the evaluator, the denotation and the value checks given,
    and the interpreter store's entries in Strata's association list `Map`.  Runtime values are
    compared by syntactic equality (`eqModuloMeta`), as fits a language whose expressions carry no
    metadata.  A language whose `P.Val` is `P.Expr` passes `boundedEval := fun _ => P.eval` and
    `denote := fun _ e => some e`. -/
@[expose, reducible] def InterpLang.withMap [DecidableEq P.Ident] [DecidableEq P.Expr]
    (ops : ReplayValueOps P P.Factory)
    (boundedEval : Nat → P.Factory → RStore P → P.Expr → Option P.Expr)
    (denote : P.Factory → P.Expr → Option P.Val)
    (typeOf : P.Factory → P.Expr → Option P.Ty) :
    InterpLang P where
  RFactory := P.Factory
  rfactory := id
  ops := ops
  boundedEval := boundedEval
  denote := denote
  typeOf := typeOf
  eqModuloMeta a b := decide (a = b)
  Writes := Map P.Ident (Option P.Expr)
  writesEmpty := []
  writesFind? := Map.find?
  writesInsert := Map.insert
  writesErase := Map.erase
  writesFind?_empty _ := rfl
  writesFind?_insert_self := Map.find?_insert_self
  writesFind?_insert_ne _ _ _ _ h := Map.find?_insert_ne _ _ _ _ h
  writesFind?_erase_self := Map.find?_erase_self
  writesFind?_erase_ne _ _ _ h := Map.find?_erase_ne _ _ _ h

/-! ## The monadic interpreter's store and environment -/

variable [InterpLang P]

/-- The runtime events of the language. -/
abbrev IEvent (P : PureExpr) [InterpLang P] := REvent P (InterpLang.RFactory P)

/-- The monadic interpreter's store: a base store and a finite map (`InterpLang.Writes`) of the
    entries written over it. An entry `some v` binds the name to `v`, an entry `none` leaves it
    undefined; a name without an entry reads the base store. -/
structure IStore (P : PureExpr) [InterpLang P] where
  /-- The store the monadic interpreter started from. -/
  base : RStore P
  /-- The entries written over `base`, one per name. -/
  writes : InterpLang.Writes P

/-- The runtime store an interpreter store stands for. -/
@[expose] def IStore.get [DecidableEq P.Ident] (s : IStore P) : RStore P :=
  fun x => match InterpLang.writesFind? s.writes x with
    | some r => r
    | none => s.base x

/-- The interpreter store of a runtime store: that store as base, with no entries. -/
@[expose] def IStore.ofStore (σ : RStore P) : IStore P :=
  { base := σ, writes := InterpLang.writesEmpty }

/-- Bind `x` to `v`, replacing the entry of `x`. -/
@[expose] def IStore.update [DecidableEq P.Ident] (s : IStore P) (x : P.Ident) (v : P.Expr) :
    IStore P :=
  { s with writes := InterpLang.writesInsert s.writes x (some v) }

/-- Leave every name of `D` undefined: erase its entry when the base store leaves it undefined,
    else replace its entry by an undefined one. -/
@[expose] def IStore.drop [DecidableEq P.Ident] (D : List P.Ident) (s : IStore P) : IStore P :=
  { s with
    writes := D.foldl
      (fun w x => if (s.base x).isSome then InterpLang.writesInsert w x none
        else InterpLang.writesErase w x)
      s.writes }

/-- Positionally bind names to values (`IStore.update`, in order). Extra names or extra values are
    dropped. -/
@[expose] def IStore.bindPositional [DecidableEq P.Ident] (s : IStore P) (names : List P.Ident)
    (values : List P.Expr) : IStore P :=
  match names, values with
  | name :: names, value :: values => (s.update name value).bindPositional names values
  | _, _ => s

/-- The monadic interpreter's environment: `Env` with an interpreter store and the runtime
    factory. -/
structure IEnv (P : PureExpr) [InterpLang P] where
  /-- The current variable store. -/
  store : IStore P
  /-- The read-only runtime factory used to evaluate expressions. -/
  factory : InterpLang.RFactory P

variable [DecidableEq P.Ident] in
/-- The environment an interpreter environment stands for under the factory `F`. -/
@[expose] def IEnv.abs (F : P.Factory) (e : IEnv P) : Env P :=
  { store := InterpLang.absStore F e.store.get, factory := F }

/-- The event argument a runtime event argument stands for under the factory `F`. -/
@[expose] def REventArg.abs (F : P.Factory) (a : REventArg P (InterpLang.RFactory P)) :
    EventArg P :=
  { factory := F, store := InterpLang.absStore F a.store, label := a.label, expr := a.expr,
    metadata := a.metadata }

/-- The event a runtime event stands for under the factory `F`. -/
@[expose] def REvent.abs (F : P.Factory) : IEvent P → Event P
  | .assert a => .assert (a.abs F)
  | .assume a => .assume (a.abs F)
  | .cover a => .cover (a.abs F)

/-- The interpreter environment of a runtime store under the runtime factory `rf`. -/
@[expose] def IEnv.ofStore (σ : RStore P) (rf : InterpLang.RFactory P) : IEnv P :=
  { store := .ofStore σ, factory := rf }

/-! ## Scope frames -/

/-- The scope frame of a block: the parent store at block entry, and, for a block the
    monadic interpreter opened, the names the block has defined (`defined = some D`). A block
    built with no recorded names has `defined = none`. -/
structure ScopeFrame (P : PureExpr) [InterpLang P] where
  /-- The store at block entry. -/
  parent : IStore P
  /-- The names the block has defined, for a block the monadic interpreter opened. -/
  defined : Option (List P.Ident)


/-- The store after exiting a block with frame `fr` from the inner store `σ`: drop the block's
    names, or, for an embedded block, project through the parent store. -/
@[expose] def ScopeFrame.exit [DecidableEq P.Ident] (fr : ScopeFrame P) (σ : IStore P) :
    IStore P :=
  match fr.defined with
  | some D => σ.drop D
  | none => .ofStore (RStore.project fr.parent.get σ.get)

/-- The frame a block opened at store `σ` starts with. -/
@[expose] def ScopeFrame.opened (σ : IStore P) : ScopeFrame P :=
  { parent := σ, defined := some [] }

/-! ## The configuration type -/

/-- The monadic interpreter's configuration: `Config` with a scope frame at each block. -/
inductive IConfig (P : PureExpr) [InterpLang P] (CmdT : Type) : Type where
  /-- A single statement to execute next. -/
  | stmt : Stmt P CmdT → IEnv P → IConfig P CmdT
  /-- A list of statements to execute next, in order. -/
  | stmts : List (Stmt P CmdT) → IEnv P → IConfig P CmdT
  /-- Execution has finished. -/
  | terminal : IEnv P → IConfig P CmdT
  /-- An exit to the block with the given label. -/
  | exiting : String → IEnv P → IConfig P CmdT
  /-- A block context with its label and scope frame. -/
  | block : Option String → ScopeFrame P → IConfig P CmdT → IConfig P CmdT
  /-- A sequence context: the inner configuration, then the remaining statements. -/
  | seq : IConfig P CmdT → List (Stmt P CmdT) → IConfig P CmdT
  /-- The inner configuration under `k + 1` sequence contexts with no remaining statements. -/
  | seqs : IConfig P CmdT → Nat → IConfig P CmdT

/-- `c` under `k` sequence contexts with no remaining statements. -/
@[expose] def Config.wrapSeqs (c : Config P CmdT) : Nat → Config P CmdT
  | 0 => c
  | k + 1 => .seq (c.wrapSeqs k) []

/-- `c` under one more sequence context with no remaining statements, as a sequence tower: a tower
    grows by one level, any other configuration becomes a tower of height one. -/
@[expose] def IConfig.seqNil : IConfig P CmdT → IConfig P CmdT
  | .seqs inner k => .seqs inner (k + 1)
  | c => .seqs c 0

/-- `c` under `k` interpreter sequence contexts `.seq · []`. -/
@[expose] def IConfig.wrapSeqs (c : IConfig P CmdT) : Nat → IConfig P CmdT
  | 0 => c
  | k + 1 => .seq (c.wrapSeqs k) []

/-- The configuration with every sequence tower expanded into nested `.seq · []` contexts. -/
@[expose] def IConfig.unseqs : IConfig P CmdT → IConfig P CmdT
  | .seqs inner k => inner.unseqs.wrapSeqs (k + 1)
  | .seq inner ss => .seq inner.unseqs ss
  | .block l fr inner => .block l fr inner.unseqs
  | c => c

/-- The semantic configuration an interpreter configuration stands for under the factory `F`:
    each runtime store becomes the semantic store it denotes (`InterpLang.absStore F`), each frame
    its parent store, and each environment's factory `F`. -/
@[expose] def IConfig.abs [DecidableEq P.Ident] (F : P.Factory) :
    IConfig P CmdT → Config P CmdT
  | .stmt s env => .stmt s (env.abs F)
  | .stmts ss env => .stmts ss (env.abs F)
  | .terminal env => .terminal (env.abs F)
  | .exiting l env => .exiting l (env.abs F)
  | .block l fr inner => .block l (InterpLang.absStore F fr.parent.get) (inner.abs F)
  | .seq inner ss => .seq (inner.abs F) ss
  | .seqs inner k => (inner.abs F).wrapSeqs (k + 1)

/-- Every runtime store of the configuration (each environment's store and each frame's parent
    store) denotes under `F` (`RStore.Denoting`), and every environment carries the runtime
    factory `InterpLang.rfactory F`. -/
@[expose] def IConfig.Denoting [DecidableEq P.Ident] (F : P.Factory) : IConfig P CmdT → Prop
  | .stmt _ env | .stmts _ env | .terminal env | .exiting _ env =>
    RStore.Denoting F env.store.get ∧ env.factory = InterpLang.rfactory F
  | .block _ fr inner => RStore.Denoting F fr.parent.get ∧ inner.Denoting F
  | .seq inner _ => inner.Denoting F
  | .seqs inner _ => inner.Denoting F

/-- The environment of the configuration's leaf. -/
@[expose] def IConfig.getEnv : IConfig P CmdT → IEnv P
  | .stmt _ ρ | .stmts _ ρ | .terminal ρ | .exiting _ ρ => ρ
  | .block _ _ inner => inner.getEnv
  | .seq inner _ => inner.getEnv
  | .seqs inner _ => inner.getEnv

/-- The store of the configuration's leaf. -/
@[expose] def IConfig.getStore [DecidableEq P.Ident] (c : IConfig P CmdT) : RStore P :=
  c.getEnv.store.get

/-- The store of the configuration's level: the parent store of the topmost block below a `.seq`
    spine, or the leaf store when there is none. -/
@[expose] def IConfig.lvl [DecidableEq P.Ident] : IConfig P CmdT → RStore P
  | .seq inner _ => inner.lvl
  | .seqs inner _ => inner.lvl
  | .block _ fr _ => fr.parent.get
  | .stmt _ env | .stmts _ env | .terminal env | .exiting _ env => env.store.get

/-- The command the next step runs at the configuration's level (not inside a nested block). -/
@[expose] def IConfig.levelCmd? : IConfig P CmdT → Option CmdT
  | .stmt (.cmd c) _ => some c
  | .seq inner _ => inner.levelCmd?
  | .seqs inner _ => inner.levelCmd?
  | _ => none

/-- The semantic counterpart of `IConfig.lvl`. -/
@[expose] def Config.lvl : Config P CmdT → SemanticStore P
  | .seq inner _ => inner.lvl
  | .block _ σ _ => σ
  | .stmt _ env | .stmts _ env | .terminal env | .exiting _ env => env.store

/-- The semantic counterpart of `IConfig.levelCmd?`. -/
@[expose] def Config.levelCmd? : Config P CmdT → Option CmdT
  | .stmt (.cmd c) _ => some c
  | .seq inner _ => inner.levelCmd?
  | _ => none

/-- The frame after a step of the block's inner configuration whose level command is `c?`
    (`IConfig.levelCmd?`): a step running the command `c` at the block's level adds the names
    of `CmdDefs.defs c` the parent store does not define. -/
@[expose] def ScopeFrame.record [DecidableEq P.Ident] [CmdDefs P CmdT] (fr : ScopeFrame P)
    (c? : Option CmdT) :
    ScopeFrame P :=
  match fr.defined, c? with
  | some D, some c =>
    { fr with
      defined := some ((CmdDefs.defs (P := P) c).filter (fun x => (fr.parent.get x).isNone) ++ D) }
  | _, _ => fr

/-! ## Exact frames -/

/-- The frame's names are exact for the inner level store `σ`: no listed name is defined in the
    parent store, and every name `σ` defines beyond the parent store is listed. -/
@[expose] def ScopeFrame.Exact [DecidableEq P.Ident] (fr : ScopeFrame P) (σ : RStore P) :
    Prop :=
  ∀ D, fr.defined = some D → ∀ x,
    (x ∈ D → fr.parent.get x = none) ∧ ((fr.parent.get x).isNone → (σ x).isSome → x ∈ D)

/-- Every frame on the configuration's spine is exact for its inner level store. -/
@[expose] def IConfig.Tracked [DecidableEq P.Ident] : IConfig P CmdT → Prop
  | .seq inner _ => inner.Tracked
  | .seqs inner _ => inner.Tracked
  | .block _ fr inner => fr.Exact inner.lvl ∧ inner.Tracked
  | _ => True

/-! ## Denotation of a semantic configuration -/

/-- The interpreter configuration `c` denotes the semantic configuration `d` under `F`: `c`'s
    stores denote (`IConfig.Denoting`), its frames are exact (`IConfig.Tracked`, which holds of
    every configuration without frames), and `c` stands for `d` (`IConfig.abs`). -/
@[expose] def IConfig.Denotes [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT)
    (d : Config P CmdT) : Prop :=
  c.Denoting F ∧ c.Tracked ∧ c.abs F = d

/-! ## Replay candidates -/

/-- A candidate counterexample for program replay: a start configuration of the monadic
    interpreter (over runtime stores) and the oracle of nondeterministic runtime values replay
    consumes from it.  It carries no fuel; replay fuel is an explicit argument of every replay
    function. -/
structure CexA (P : PureExpr) [InterpLang P] (CmdT : Type) where
  cfg : IConfig P CmdT
  oracle : List P.Expr

end -- public section

end Imperative
