/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.CoreOp
import all Strata.Languages.Core.CoreOp
public import Strata.Languages.Core.NameMangling
import all Strata.Languages.Core.NameMangling
public import Strata.DL.SMT.Factory
import all Strata.DL.SMT.Factory
public import Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.TypeFactory
public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
public import Strata.DL.Imperative.EvalContext
import all Strata.DL.Imperative.EvalContext
public import Strata.Util.Name
import all Strata.Util.Name
public import StrataDDM.Util.DecimalRat
import all StrataDDM.Util.DecimalRat
-- Language-definition files (single source of truth for the data types + judgments the encoder builds
-- on): `CoreCtx`/`FnDef`/`VarDef`/`RConstructor`/`collectArrowTy`/`KnownTypeArities` are defined there
-- and reused here (dependency flows language files → encoder → proof files). The SMT-side `SMTQuery`
-- target language is imported from `DL/SMT` below.
import Strata.Languages.Core.VerifiedSMTGen.Expression
public import Strata.Languages.Core.VerifiedSMTGen.CoreCtx
import all Strata.Languages.Core.VerifiedSMTGen.CoreCtx
public import Strata.DL.SMT.DenoteTypedSMTQuery
import all Strata.DL.SMT.DenoteTypedSMTQuery
-- `datatypeOpNames` (the datatype-op name set of a type factory) lives here.
import Strata.Languages.Core.VerifiedSMTGen.ProofObligation
import all Strata.Languages.Core.VerifiedSMTGen.ProofObligation

/-!
# Core → SMT encoder

Encodes a Core `ProofObligation` into an SMT query and renders it to SMT-LIB text. The encoder runs in
two phases: `collect` resolves the Core-level facts an obligation depends on (reachable functions,
datatypes, opaque sorts, free variables) into a by-kind `CoreCtx`, and `translate` turns that context
and the obligation's expressions into `Strata.SMT.Term`s and an `SMTQuery`.

## Coverage

Booleans (And/Or/Not/Implies/Equiv), integer and real arithmetic and comparisons, bitvectors
(including safe and overflow-predicate operations), strings, regex, triggers, truncating div/mod, and
maps (native Array theory or uninterpreted). Operators outside this set map to `none` (an encoder
error).
-/

open Core Lambda Imperative Strata.SMT Std
open Strata.SMT.DenoteTyped

namespace Core.Refactor

/-- Maps a predefined `CoreOp` to its SMT term builder `List Term → TermType → Term`, or `none` for
    operators with no direct builder (which fall to the uninterpreted-function path). The builder
    receives the annotation-derived result sort, letting it handle polymorphic-return operators
    (`Map` `select`/`update`) and width-dependent `bvconcat`.

    `useArrayTheory` routes `Map` `select`/`update` to the native SMT Array ops (`Op.select`/`Op.store`)
    when on; when off they return `none` and fall to the uninterpreted path. `Map` `const` is always
    `none`. Covers booleans, integer/real arithmetic and comparisons, bitvectors (including safe and
    overflow-predicate ops), strings, regex, triggers, and truncating div/mod. -/
def corePredefinedOpToSMTOp (useArrayTheory : Bool) (op : CoreOp) :
    Option (List Term → TermType → Term) :=
  match op with
  -- Booleans
  | .bool .And     => some (.app Op.and)
  | .bool .Or      => some (.app Op.or)
  | .bool .Not     => some (.app Op.not)
  | .bool .Implies => some (.app Op.implies)
  | .bool .Equiv   => some (.app Op.eq)
  -- Integer arithmetic
  | .numeric ⟨.int, .Neg⟩ => some (.app Op.neg)
  | .numeric ⟨.int, .Add⟩ => some (.app Op.add)
  | .numeric ⟨.int, .Sub⟩ => some (.app Op.sub)
  | .numeric ⟨.int, .Mul⟩ => some (.app Op.mul)
  | .numeric ⟨.int, .Div⟩ | .numeric ⟨.int, .SafeDiv⟩ => some (.app Op.div)
  | .numeric ⟨.int, .Mod⟩ | .numeric ⟨.int, .SafeMod⟩ => some (.app Op.mod)
  -- Truncating division: tdiv(a,b) = ite(a*b ≥ 0, ediv(|a|,|b|), -ediv(|a|,|b|))
  | .numeric ⟨.int, .DivT⟩ | .numeric ⟨.int, .SafeDivT⟩ =>
    some fun (args : List Term) (retTy : TermType) =>
      match args with
      | [a, b] =>
        let ab := Term.app Op.mul [a, b] retTy
        let abGeZero := Term.app Op.ge [ab, Term.prim (.int 0)] .bool
        let q := Term.app Op.div [Term.app Op.abs [a] retTy, Term.app Op.abs [b] retTy] retTy
        Factory.ite abGeZero q (Term.app Op.neg [q] retTy)
      | _ => Term.app Op.div args retTy
  -- Truncating modulo: tmod(a,b) = a - b * tdiv(a,b)
  | .numeric ⟨.int, .ModT⟩ | .numeric ⟨.int, .SafeModT⟩ =>
    some fun (args : List Term) (retTy : TermType) =>
      match args with
      | [a, b] =>
        let ab := Term.app Op.mul [a, b] retTy
        let abGeZero := Term.app Op.ge [ab, Term.prim (.int 0)] .bool
        let q := Term.app Op.div [Term.app Op.abs [a] retTy, Term.app Op.abs [b] retTy] retTy
        let tdivAB := Term.app Op.ite [abGeZero, q, Term.app Op.neg [q] retTy] retTy
        Term.app Op.sub [a, Term.app Op.mul [b, tdivAB] retTy] retTy
      | _ => Term.app Op.mod args retTy
  -- Integer comparisons
  | .numeric ⟨.int, .Lt⟩ => some (.app Op.lt)
  | .numeric ⟨.int, .Le⟩ => some (.app Op.le)
  | .numeric ⟨.int, .Gt⟩ => some (.app Op.gt)
  | .numeric ⟨.int, .Ge⟩ => some (.app Op.ge)
  -- Real arithmetic + comparisons
  | .numeric ⟨.real, .Neg⟩ => some (.app Op.neg)
  | .numeric ⟨.real, .Add⟩ => some (.app Op.add)
  | .numeric ⟨.real, .Sub⟩ => some (.app Op.sub)
  | .numeric ⟨.real, .Mul⟩ => some (.app Op.mul)
  | .numeric ⟨.real, .Div⟩ => some (.app Op.rdiv)
  | .numeric ⟨.real, .Lt⟩  => some (.app Op.lt)
  | .numeric ⟨.real, .Le⟩  => some (.app Op.le)
  | .numeric ⟨.real, .Gt⟩  => some (.app Op.gt)
  | .numeric ⟨.real, .Ge⟩  => some (.app Op.ge)
  | .numeric ⟨_, _⟩ => none
  -- Bitvector operations (size-generic)
  | .bv ⟨_, .Neg⟩  => some (.app Op.bvneg)
  | .bv ⟨_, .Add⟩  => some (.app Op.bvadd)
  | .bv ⟨_, .Sub⟩  => some (.app Op.bvsub)
  | .bv ⟨_, .Mul⟩  => some (.app Op.bvmul)
  | .bv ⟨_, .UDiv⟩ => some (.app Op.bvudiv)
  | .bv ⟨_, .UMod⟩ => some (.app Op.bvurem)
  | .bv ⟨_, .SDiv⟩ => some (.app Op.bvsdiv)
  | .bv ⟨_, .SMod⟩ => some (.app Op.bvsrem)
  | .bv ⟨_, .Not⟩  => some (.app Op.bvnot)
  | .bv ⟨_, .And⟩  => some (.app Op.bvand)
  | .bv ⟨_, .Or⟩   => some (.app Op.bvor)
  | .bv ⟨_, .Xor⟩  => some (.app Op.bvxor)
  | .bv ⟨_, .Shl⟩  => some (.app Op.bvshl)
  | .bv ⟨_, .UShr⟩ => some (.app Op.bvlshr)
  | .bv ⟨_, .SShr⟩ => some (.app Op.bvashr)
  | .bv ⟨_, .ULt⟩  => some (.app Op.bvult)
  | .bv ⟨_, .ULe⟩  => some (.app Op.bvule)
  | .bv ⟨_, .UGt⟩  => some (.app Op.bvugt)
  | .bv ⟨_, .UGe⟩  => some (.app Op.bvuge)
  | .bv ⟨_, .SLt⟩  => some (.app Op.bvslt)
  | .bv ⟨_, .SLe⟩  => some (.app Op.bvsle)
  | .bv ⟨_, .SGt⟩  => some (.app Op.bvsgt)
  | .bv ⟨_, .SGe⟩  => some (.app Op.bvsge)
  | .bv ⟨_, .Concat⟩ => some (.app Op.bvconcat)
  | .bv ⟨_, .ToUInt⟩ => some (.app Op.ubv_to_int)
  | .bv ⟨_, .ToInt⟩  => some (.app Op.sbv_to_int)
  | .intToBv n       => some (.app (Op.int_to_bv n))
  -- Safe BV ops (same encoding as unsafe; preconditions checked upstream)
  | .bv ⟨_, .SafeAdd⟩  => some (.app Op.bvadd)
  | .bv ⟨_, .SafeSub⟩  => some (.app Op.bvsub)
  | .bv ⟨_, .SafeMul⟩  => some (.app Op.bvmul)
  | .bv ⟨_, .SafeNeg⟩  => some (.app Op.bvneg)
  | .bv ⟨_, .SafeUAdd⟩ => some (.app Op.bvadd)
  | .bv ⟨_, .SafeUSub⟩ => some (.app Op.bvsub)
  | .bv ⟨_, .SafeUMul⟩ => some (.app Op.bvmul)
  | .bv ⟨_, .SafeUNeg⟩ => some (.app Op.bvneg)
  | .bv ⟨_, .SafeSDiv⟩ => some (.app Op.bvsdiv)
  | .bv ⟨_, .SafeSMod⟩ => some (.app Op.bvsrem)
  -- Signed overflow predicates
  | .bv ⟨_, .SAddOverflow⟩ => some (.app Op.bvsaddo)
  | .bv ⟨_, .SSubOverflow⟩ => some (.app Op.bvssubo)
  | .bv ⟨_, .SMulOverflow⟩ => some (.app Op.bvsmulo)
  | .bv ⟨_, .SNegOverflow⟩ => some (.app Op.bvnego)
  | .bv ⟨n, .SDivOverflow⟩ =>
    some fun (args : List Term) (_retTy : TermType) =>
      match args with
      | [x, y] =>
        let xIsMin := Term.app Op.eq [x, Term.prim (.bitvec (BitVec.intMin n))] .bool
        let yIsNegOne := Term.app Op.eq [y, Term.prim (.bitvec (BitVec.allOnes n))] .bool
        Term.app Op.and [xIsMin, yIsNegOne] .bool
      | _ => Term.app Op.and [] .bool
  -- Unsigned overflow predicates
  | .bv ⟨_, .UAddOverflow⟩ =>
    some fun (args : List Term) (_retTy : TermType) =>
      match args with
      | [x, y] =>
        let sum := Term.app Op.bvadd [x, y] x.typeOf
        Term.app Op.bvult [sum, x] .bool
      | _ => Term.app Op.and [] .bool
  | .bv ⟨_, .USubOverflow⟩ => some (Term.app Op.bvult)
  | .bv ⟨n, .UMulOverflow⟩ =>
    some fun (args : List Term) (_retTy : TermType) =>
      match args with
      | [x, y] =>
        let extTy := TermType.prim (.bitvec (n + n))
        let prod := Term.app Op.bvmul [Term.app (.zero_extend n) [x] extTy,
                                       Term.app (.zero_extend n) [y] extTy] extTy
        let maxExt := Term.app (.zero_extend n) [Term.prim (.bitvec (BitVec.allOnes n))] extTy
        Term.app Op.bvugt [prod, maxExt] .bool
      | _ => Term.app Op.and [] .bool
  | .bv ⟨n, .UNegOverflow⟩ =>
    some fun (args : List Term) (_retTy : TermType) =>
      match args with
      | [x] => Term.app Op.not [Term.app Op.eq [x, Term.prim (.bitvec (BitVec.zero n))] .bool] .bool
      | _ => Term.app Op.and [] .bool
  -- Strings
  | .str .Length   => some (.app Op.str_length)
  | .str .Concat   => some (.app Op.str_concat)
  | .str .Substr   => some (.app Op.str_substr)
  | .str .ToRegEx  => some (.app Op.str_to_re)
  | .str .InRegEx  => some (.app Op.str_in_re)
  | .str .PrefixOf => some (.app Op.str_prefixof)
  | .str .SuffixOf => some (.app Op.str_suffixof)
  | .str .Contains => some (.app Op.str_contains)
  | .str .IndexOf  => some (.app Op.str_indexof)
  | .str .Replace  => some (.app Op.str_replace)
  | .str .At       => some (.app Op.str_at)
  | .str .Lt       => some (.app Op.str_lt)
  | .str .Le       => some (.app Op.str_le)
  -- Regex
  | .re .All     => some (.app Op.re_all)
  | .re .AllChar => some (.app Op.re_allchar)
  | .re .Range   => some (.app Op.re_range)
  | .re .Concat  => some (.app Op.re_concat)
  | .re .Star    => some (.app Op.re_star)
  | .re .Plus    => some (.app Op.re_plus)
  | .re .Union   => some (.app Op.re_union)
  | .re .Inter   => some (.app Op.re_inter)
  | .re .Comp    => some (.app Op.re_comp)
  | .re .None    => some (.app Op.re_none)
  -- `re.loop`'s two Nat bounds are op parameters extracted from the call-site spine in
  -- `translateAppHead`, not a flat builder; this arm supplies only a degenerate fallback so `re.loop` is
  -- recognized as predefined (excluded from the function walk).
  | .re .Loop    => some (fun args _ => Term.app (Op.re_loop 0 0) args .regex)
  -- Maps (Array theory): native `select`/`store` only when `useArrayTheory`; else UF path.
  | .map .Select => if useArrayTheory then some (.app Op.select) else none
  | .map .Update => if useArrayTheory then some (.app Op.store) else none
  | .map .Const  => none  -- always UF (no native Array builder for constant maps)
  -- Trigger meta-ops (`Triggers.*` / `TriggerGroup.*`): recognized as predefined so they are EXCLUDED
  -- from the reachable-function walk (`exprFnRefs`), but their builder is NEVER invoked — the `.quant`
  -- translate arm lowers a quantifier's trigger structurally into `List (List Term)` pattern groups (see
  -- `translateTriggerGroups`), so a trigger op never reaches `translateAppHead`. `Term.quant` carries
  -- `List (List Term)` directly; there is no flat trigger op/term to build here, so this degenerate
  -- builder exists only to satisfy the return type.
  | .trigger _ => some (fun _ _ => Term.prim (.bool true))
  | _ => none

/-! ## Two-phase encoder: `CoreCtx` + `collect` + `translate`

  • `collect` resolves the Core-level questions — which functions, datatypes, and sorts an obligation
    reaches — and produces a `CoreCtx` (below) plus the SMT-declaration reachability closures.
  • `translate` is a pure `(CoreCtx, bvs, e) → Term`.

`CoreCtx` carries the resolved facts grouped by kind: function declarations/definitions, their axioms,
variable declarations/definitions, program-level assumptions, and distinct groups. Datatype-op
resolution, type-variable resolution, and a name supply are additional `CoreCtx` fields. -/

-- `FnDef` (+ `FnDef.argTys`/`argNames`) and `VarDef` are defined in `VerifiedSMTGen.CoreCtx` (imported above).

/-! ### Reference extraction (function + type reachability seeds)

Pure Core-level machinery for the reachability walks, in two clusters (the closures themselves,
`collectFuncsGo`/`collectTypesGo`, come later since they thread `CoreCtx`):

  • Function side: `exprFnRefs`, `funcFnRefs`, `funcBvarSubst` — seeds for the reachable
    factory-function closure.
  • Type side: `isBuiltinTyName`, `tyNameRefs`, `exprTypeRefs`, `funcTypeRefs`, `dtConstrRefs`,
    `datatypeOpNames`, `datatypeFunsOf` — the type analog, resolving both datatypes and opaque sorts.
    `tyNameRefs`/`exprTypeRefs`/`funcTypeRefs` are the seeds, `dtConstrRefs` the reference edge, and
    `collectTypesGo` (below) the worklist closure. Built-in base types (`bool`/`int`/`real`/`string`/
    `regex` and the structural `arrow`) are skipped. -/

/-- Function references an expression makes at applied `.op` heads — each as a factory-function name —
    skipping predefined operators, which need no declaration. The factory is monomorphic, so the name
    alone identifies the instance. -/
def exprFnRefs (useArrayTheory : Bool) : Expression.Expr → List String
  | .op () o _oty       =>
    -- Classify on the demangled base name, so a mangled predefined op (e.g. `select`/`update`) is
    -- recognized and skipped rather than collected as a UF. `demangledBaseName` is the identity on
    -- unmangled names.
    if (corePredefinedOpToSMTOp useArrayTheory (CoreOp.ofString (Core.NameMangling.demangledBaseName o.name))).isSome then []
    else [o.name]
  | .app () fn e        => exprFnRefs useArrayTheory fn ++ exprFnRefs useArrayTheory e
  | .ite () c t e       => exprFnRefs useArrayTheory c ++ exprFnRefs useArrayTheory t ++ exprFnRefs useArrayTheory e
  | .eq () e1 e2        => exprFnRefs useArrayTheory e1 ++ exprFnRefs useArrayTheory e2
  | .abs () _ _ e       => exprFnRefs useArrayTheory e
  | .quant () _ _ _ tr e => exprFnRefs useArrayTheory tr ++ exprFnRefs useArrayTheory e
  | _                   => []

/-- Factory-function names a factory function references, from its body and each of its axioms.
    A **recursive** function is emitted as an uninterpreted `declare-fun` — its body is dropped from the
    SMT output, so callees referenced only within that body need not be declared; and its body may not
    even be well-typed at the point-of-definition context (it can call mutually-recursive functions that
    come LATER in the factory). So the body is walked only for NON-recursive functions; recursive
    functions contribute their axioms' references (the axioms ARE emitted, and are well-typed). -/
def funcFnRefs (useArrayTheory : Bool) (f : LFunc CoreLParams) : List String :=
  (if f.isRecursive then [] else f.body.map (exprFnRefs useArrayTheory) |>.getD [])
    ++ f.axioms.flatMap (exprFnRefs useArrayTheory)

-- `funcBvarSubst` is defined in `Expression` (imported above).

/-- Whether a type name maps to a native SMT sort (never a `declare-sort`/`declare-datatype`), so the
    type walk skips it: `bool`/`int`/`real`/`string`/`regex` and the structural `arrow`, plus `Map` when
    `useArrayTheory` (routed to Array theory). -/
def isBuiltinTyName (useArrayTheory : Bool) (id : String) : Bool :=
  id ∈ ["bool", "int", "real", "string", "regex", "arrow"] ∨ (useArrayTheory ∧ id == "Map")

/-- Type names a monomorphic type mentions (transitively through type arguments), skipping
    native-sort names. A `.tcons name args` contributes `name` (unless native) plus the refs of
    each argument; `.ftvar`/`.bitvec` contribute nothing. -/
def tyNameRefs (useArrayTheory : Bool) : LMonoTy → List String
  | .tcons name args =>
    let argRefs := args.flatMap (tyNameRefs useArrayTheory)
    if isBuiltinTyName useArrayTheory name then argRefs else name :: argRefs
  | _ => []

/-- Datatype/sort names an expression mentions in its type annotations — `.op`/`.fvar` arrow signatures
    and binder types (`.abs`/`.quant`). The type-side seed analog of `exprFnRefs`. -/
def exprTypeRefs (useArrayTheory : Bool) : Expression.Expr → List String
  | .op () _ ty         => (ty.map (tyNameRefs useArrayTheory)).getD []
  | .fvar () _ ty       => (ty.map (tyNameRefs useArrayTheory)).getD []
  | .app () fn e        => exprTypeRefs useArrayTheory fn ++ exprTypeRefs useArrayTheory e
  | .ite () c t e       => exprTypeRefs useArrayTheory c ++ exprTypeRefs useArrayTheory t ++ exprTypeRefs useArrayTheory e
  | .eq () e1 e2        => exprTypeRefs useArrayTheory e1 ++ exprTypeRefs useArrayTheory e2
  | .abs () _ ty e      => (ty.map (tyNameRefs useArrayTheory)).getD [] ++ exprTypeRefs useArrayTheory e
  | .quant () _ _ ty tr e =>
    (ty.map (tyNameRefs useArrayTheory)).getD [] ++ exprTypeRefs useArrayTheory tr ++ exprTypeRefs useArrayTheory e
  | _                   => []

/-- Datatype/sort names a factory function's signature mentions (argument + return types). Seeding the
    type walk from these — for every reachable function — catches types that surface only in a reachable
    function's signature. -/
def funcTypeRefs (useArrayTheory : Bool) (f : LFunc CoreLParams) : List String :=
  (f.inputs.toList.flatMap (fun (_, ty) => tyNameRefs useArrayTheory ty)) ++ tyNameRefs useArrayTheory f.output

/-- Datatype names referenced by a datatype's own constructor field types — the reference edge of the
    datatype closure. A datatype transitively reaches every datatype appearing in any constructor's
    argument types. -/
def dtConstrRefs (useArrayTheory : Bool) (d : LDatatype CoreLParams.IDMeta) : List String :=
  d.constrs.flatMap (fun c => c.args.flatMap (fun (_, ty) => tyNameRefs useArrayTheory ty))

-- `datatypeOpNames` is defined in `ProofObligation` (imported above).

/-- The datatype-op index contributed by one datatype: op name → (kind, defining constructor), for its
    constructor / tester / (safe + unsafe) selector names. Each name is tagged with its
    `Op.DatatypeFuncs` kind (unsafe selectors share the `.selector` kind) and unioned first-binding-wins. -/
def datatypeFunsOf (d : LDatatype CoreLParams.IDMeta) :
    Map String (Op.DatatypeFuncs × LConstr CoreLParams.IDMeta) :=
  let (c, i, s, u) := d.genFunctionMaps
  let tag := fun (kind : Op.DatatypeFuncs)
      (entries : Map String (LDatatype CoreLParams.IDMeta × LConstr CoreLParams.IDMeta)) =>
    Map.ofList (entries.toList.map (fun (name, _, c) => (name, (kind, c))))
  (tag Op.DatatypeFuncs.constructor c)
    |>.union (tag Op.DatatypeFuncs.tester i)
    |>.union (tag Op.DatatypeFuncs.selector s)
    |>.union (tag Op.DatatypeFuncs.selector u)

/-! ### Assumed inputs — `KnownTypeArities`, `SurroundingCtx`

The contexts the encoder assumes rather than derives, alongside `F : Factory` / `tf : TypeFactory`:
the type-arity registry the type closure resolves opaque sorts against, and the unmanaged free-variable
context (`fctx`), bundled together in `SurroundingCtx`. -/

-- `KnownTypeArities` is defined in `VerifiedSMTGen.CoreCtx` (imported above).

/-- The four surrounding contexts an obligation is closed over — the encoder's assumed inputs, the
    typing environment against which a post-evaluation `ProofObligation` is well-formed. Each closes one
    kind of free symbol: `F` (functions), `tf` (datatypes/type constructors), `karities` (opaque sorts),
    `fctx` (unmanaged free variables). -/
structure SurroundingCtx where
  /-- Function factory — closes reachable function references. -/
  F : Lambda.Factory CoreLParams
  /-- Type factory — closes reachable datatypes / type constructors. -/
  tf : @Lambda.TypeFactory CoreLParams.IDMeta
  /-- Opaque-sort arities — closes abstract `(declare-sort name arity)` type names. -/
  karities : KnownTypeArities
  /-- Unmanaged free-variable context — closes free `.fvar` names with no in-obligation binding site. -/
  fctx : List (String × LMonoTy)

-- `CoreCtx` (the by-kind collected context) is defined in `VerifiedSMTGen.CoreCtx` (imported above).

/-- Phase-1 collection state: the walk bookkeeping (dedup sets) alongside the resolved context
    (`CoreCtx`). Only `ctx` is consumed downstream; `seenFns`/`seenTypes` are dedup state the closures
    thread and discard. -/
structure CollectState where
  ctx : CoreCtx := {}
  /-- Factory-function names already resolved — the function closure's visited set. A monomorphic factory
      means one declaration per name, so a plain name-set dedup suffices. -/
  seenFns : List String := []
  /-- Type names (datatypes and opaque sorts) already resolved — the type closure's visited set, so it
      neither re-materializes nor re-recurses. -/
  seenTypes : List String := []
  deriving Inhabited

/-! ## Phase 1 — `collect`

`collect` resolves Core-level facts and accumulates them, by kind, into `CoreCtx`. Its heart is the
function-reachability walk: seed from the expression's direct (non-predefined) `.op`/`.fvar`
references, transitively close over the factory following `funcFnRefs`, and materialize each newly
reachable factory function into the right `CoreCtx` chunk —
  • non-recursive with body → `fnDefs` (an SMT `define-fun`),
  • recursive or bodyless   → `fnDecls` (an SMT `declare-fun`),
plus the function's axioms into `fnAxioms`.

`collect` takes the current `CoreCtx` and seeds reachability from it, so folding it over each
expression of a `ProofObligation` accumulates into one order-independent `CoreCtx` without re-traversal.
Program-level `assumptions`/`varDecls`/`varDefs`/`distincts` are added at the obligation level. -/

/-- Mark a reachable factory-function name as seen. This is all the reachability walk (`collectFuncsGo`)
    does — accumulate the reachable-name set (`seenFns`) and follow reference edges; it does not populate
    `fnDecls`/`fnDefs`/`fnAxioms`, which are materialized afterwards by `addFunc` in factory order. -/
def CollectState.markFuncSeen (st : CollectState) (name : String) : CollectState :=
  { st with seenFns := st.seenFns ++ [name] }

/-- Materialize one already-reached factory function into the appropriate `CoreCtx` chunk (classified by
    body/recursion) and append its axioms. Does not touch `seenFns`. -/
def CollectState.addFunc (st : CollectState) (f : LFunc CoreLParams) : CollectState :=
  let inputs := f.inputs.values
  -- Formal-parameter names paired with their types, in order — the same `f.inputs.keys` list
  -- `funcBvarSubst` indexes, so the SMT binder id at position `i` matches the formal the body references
  -- positionally. Names are used only for readable output and capture-freedom.
  let params := (f.inputs.keys.map (·.name)).zip inputs
  let cctx := { st.ctx with fnAxioms := st.ctx.fnAxioms ++ f.axioms }
  let cctx :=
    match f.isRecursive, f.body with
    | false, some body =>
      let fnBody := LExpr.substFvarsLifting body (funcBvarSubst f)
      { cctx with fnDefs := cctx.fnDefs ++
          [{ name := f.name.name, params := params, retTy := f.output, body := fnBody }] }
    | _, _ =>
      { cctx with fnDecls := cctx.fnDecls ++ [(f.name.name, List.foldr LMonoTy.arrow f.output inputs)] }
  { st with ctx := cctx }

/-- Materialize `fnDecls`/`fnDefs`/`fnAxioms` for all reached functions by iterating the factory in its
    stored order (callee before caller), keeping those whose name the walk reached (`seenFns`). This
    makes `define-fun`s emit in dependency order. -/
def CollectState.materializeFuncs (st : CollectState) (F : Lambda.Factory CoreLParams) : CollectState :=
  F.toArray.foldl (fun st f => if st.seenFns.contains f.name.name then st.addFunc f else st) st

/-- Termination measure for the function walk: the count of factory functions not yet materialized
    (whose name is not in `seenFns`). -/
def CollectState.unseenFuncs (st : CollectState) (F : Lambda.Factory CoreLParams) : Nat :=
  (F.toArray.toList.filter (fun lf => decide (lf.name.name ∉ st.seenFns))).length

/-- Monotonicity of `filter` length: a pointwise-stronger predicate keeps no more. -/
private theorem filter_length_le_of_imp {α} (p q : α → Bool)
    (himp : ∀ x, q x = true → p x = true) : ∀ (l : List α),
    (l.filter q).length ≤ (l.filter p).length
  | [] => by simp
  | b :: t => by
    have ih := filter_length_le_of_imp p q himp t
    simp only [List.filter_cons]
    by_cases hp : p b = true
    · by_cases hq : q b = true
      · rw [if_pos hp, if_pos hq]; simp only [List.length_cons]; omega
      · rw [if_pos hp, if_neg hq]; simp only [List.length_cons]; omega
    · have hq : ¬ q b = true := fun h => hp (himp b h)
      rw [if_neg hp, if_neg hq]; omega

/-- Strict decrease of `filter` length: if some member fails the (stronger) predicate `q` but
    satisfies the (weaker) `p`, then `filter q` is strictly shorter than `filter p`. -/
private theorem filter_length_lt_of_mem {α} (p q : α → Bool) (a : α)
    (himp : ∀ x, q x = true → p x = true) :
    ∀ (l : List α), a ∈ l → p a = true → q a = false →
      (l.filter q).length < (l.filter p).length
  | [], ha, _, _ => by simp at ha
  | b :: t, ha, hpa, hqa => by
    have hle := filter_length_le_of_imp p q himp t
    simp only [List.filter_cons]
    rcases List.mem_cons.mp ha with rfl | hat
    · -- a = b : kept by p, dropped by q
      rw [if_pos hpa, if_neg (by simp [hqa])]
      simp only [List.length_cons]; omega
    · -- a ∈ t
      have ih := filter_length_lt_of_mem p q a himp t hat hpa hqa
      by_cases hp : p b = true
      · by_cases hq : q b = true
        · rw [if_pos hp, if_pos hq]; simp only [List.length_cons]; omega
        · rw [if_pos hp, if_neg hq]; simp only [List.length_cons]; omega
      · have hq : ¬ q b = true := fun h => hp (himp b h)
        rw [if_neg hp, if_neg hq]; omega

/-- Each `addFunc` strictly shrinks the unseen-function count: it records `name`, a factory function
    (from `F[name]? = some f`) not previously in `seenFns`. -/
private theorem markFuncSeen_unseenFuncs_lt {F : Lambda.Factory CoreLParams}
    {st : CollectState} {name : String} {f : LFunc CoreLParams}
    (hget : F[name]? = some f) (hns : name ∉ st.seenFns) :
    (st.markFuncSeen name).unseenFuncs F < st.unseenFuncs F := by
  have hseen : (st.markFuncSeen name).seenFns = st.seenFns ++ [name] := rfl
  have hfmem : f ∈ F.toArray := Lambda.Factory.getElem?_is_some_implies_mem hget
  have hfname : f.name.name = name := Lambda.Factory.getElem?_name hget
  unfold CollectState.unseenFuncs
  simp only [hseen]
  apply filter_length_lt_of_mem
    (fun lf => decide (lf.name.name ∉ st.seenFns))
    (fun lf => decide (lf.name.name ∉ st.seenFns ++ [name]))
    f
  · -- himp: ∉ (seenFns ++ [name]) → ∉ seenFns
    intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact fun hc => hx (List.mem_append.mpr (Or.inl hc))
  · exact Array.mem_def.mp hfmem
  · -- p f = true: f.name.name = name ∉ seenFns
    simp only [decide_eq_true_eq, hfname]; exact hns
  · -- q f = false: f.name.name = name ∈ seenFns ++ [name]
    simp only [hfname, decide_eq_false_iff_not]
    exact fun h => h (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))

set_option linter.unusedVariables false in
/-- Function-closure worklist: resolve each reachable factory-function name, materializing it (`addFunc`)
    and following its reference edges (`funcFnRefs`), dedup on the name (`st.seenFns`). Datatype ops are
    excluded (they come free with `declare-datatype`) — skipped at dequeue via `dtOps`. -/
def collectFuncsGo (useArrayTheory : Bool) (F : Lambda.Factory CoreLParams) (dtOps : List String) :
    (st : CollectState) → (worklist : List String) → CollectState
  | st, [] => st
  | st, name :: rest =>
    match h : F[name]? with
    | none => collectFuncsGo useArrayTheory F dtOps st rest
    | some f =>
      if hcond : Core.NameMangling.demangledBaseName name ∈ dtOps ∨ name ∈ st.seenFns then
        collectFuncsGo useArrayTheory F dtOps st rest
      else
        collectFuncsGo useArrayTheory F dtOps (st.markFuncSeen name) (funcFnRefs useArrayTheory f ++ rest)
  termination_by st worklist => (st.unseenFuncs F, worklist.length)
  decreasing_by
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.left _ _ (markFuncSeen_unseenFuncs_lt h (fun hn => hcond (Or.inr hn)))

/-- Accumulate all factory functions reachable from `e` (given `F`) into `st`, seeding from the
    (non-predefined) `.op` names `e` references. Excludes datatype ops (constructors / testers /
    selectors), which must not become `declare-fun`s — they are emitted as `.datatype_op`. -/
def collectFuncs (useArrayTheory : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (st : CollectState) (e : Expression.Expr) : CollectState :=
  let dtOps := datatypeOpNames tf
  collectFuncsGo useArrayTheory F dtOps st (exprFnRefs useArrayTheory e)

/-- Record one reachable datatype: its name in `seenTypes` (the reached-set that drives block regrouping
    at the end of `collectObligation`) and its functions in the datatype-op cache. The block-grouped
    `ctx.datatypes` field is populated once from the type factory at collect's end, not incrementally. -/
def CollectState.addDatatype (st : CollectState) (d : LDatatype CoreLParams.IDMeta) : CollectState :=
  { st with ctx := { st.ctx with
                                  -- first-binding-wins: already-resolved entries (the `union` LHS) win
                                  datatypeFuns := st.ctx.datatypeFuns.union (datatypeFunsOf d) },
            seenTypes := st.seenTypes ++ [d.name] }

/-- Record one reachable OPAQUE sort `(name, arity)` — the factory-MISS branch of the type closure. -/
def CollectState.addSort (st : CollectState) (name : String) (arity : Nat) : CollectState :=
  { st with ctx := { st.ctx with sorts := st.ctx.sorts ++ [(name, arity)] },
            seenTypes := st.seenTypes ++ [name] }

/-- Termination measure for the type walk: unseen names from the type-name universe
    `tf.allTypeNames ∪ karities.map (·.1)` (all declared datatypes + opaque sorts). -/
def CollectState.unseenTypes (st : CollectState) (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (karities : KnownTypeArities) : Nat :=
  ((tf.allTypeNames ++ karities.map (·.1)).filter (fun n => decide (n ∉ st.seenTypes))).length

/-- Extending `seenTypes` by a fresh in-universe name strictly shrinks the unseen count. Reused by
    both `addDatatype` and `addSort` branches of the type walk. -/
private theorem seenTypes_add_unseenTypes_lt
    (st : CollectState) (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (karities : KnownTypeArities)
    (name : String)
    (hmem : name ∈ tf.allTypeNames ∨ name ∈ karities.map (·.1))
    (hns : name ∉ st.seenTypes) :
    (((tf.allTypeNames ++ karities.map (·.1)).filter
        (fun n => decide (n ∉ st.seenTypes ++ [name]))).length)
    < ((tf.allTypeNames ++ karities.map (·.1)).filter
        (fun n => decide (n ∉ st.seenTypes))).length := by
  apply filter_length_lt_of_mem
    (fun n => decide (n ∉ st.seenTypes))
    (fun n => decide (n ∉ st.seenTypes ++ [name]))
    name
  · intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact fun hc => hx (List.mem_append.mpr (Or.inl hc))
  · exact List.mem_append.mpr hmem
  · simp only [decide_eq_true_eq]; exact hns
  · simp only [decide_eq_false_iff_not]
    exact fun h => h (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))

set_option linter.unusedVariables false in
/-- Type-closure worklist: resolve each reachable type name, materializing it into `st` and following
    its reference edges. Three outcomes per name:
      • builtin (`isBuiltinTyName`) → skip (native theory sort);
      • found in `tf` → `addDatatype` and enqueue its constructor field-type refs (`dtConstrRefs`);
      • miss → an opaque sort: look its arity up in `KnownTypeArities` and `addSort`; a name absent from
        the table is skipped (no fabricated sorts).

    The `none`-skip cannot drop a needed sort, given a consistent `(F, tf)` pair. The only opaque sorts
    this branch resolves that are not themselves datatypes are those appearing in a reachable datatype's
    constructor field types (reached via `dtConstrRefs`). Each datatype's constructors are factory
    functions whose `inputs` ARE those field types (`constrFunc`/`genBlockFactory`), and they are merged
    into `F` in lockstep with the datatype entering `tf` (`Env.addMutualDatatype`, the sole writer of
    `tf`). `karitiesOf` scans every `F` function's signature, so every such sort has an arity entry. -/
def collectTypesGo (useArrayTheory : Bool) (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (karities : KnownTypeArities) : (st : CollectState) → (worklist : List String) → CollectState
  | st, [] => st
  | st, g :: rest =>
    if hskip : isBuiltinTyName useArrayTheory g ∨ g ∈ st.seenTypes then
      collectTypesGo useArrayTheory tf karities st rest
    else match hg : tf.getType g with
      | some d => collectTypesGo useArrayTheory tf karities (st.addDatatype d) (dtConstrRefs useArrayTheory d ++ rest)
      | none   => match hk : karities.find? (·.1 == g) with
        | some (_, arity) => collectTypesGo useArrayTheory tf karities (st.addSort g arity) rest
        | none => collectTypesGo useArrayTheory tf karities st rest
  termination_by st worklist => (st.unseenTypes tf karities, worklist.length)
  decreasing_by
    · exact Prod.Lex.right _ (by simp)
    · -- addDatatype branch: `d.name = g`, `g ∈ tf.allTypeNames`, `g ∉ seenTypes`
      refine Prod.Lex.left _ _ ?_
      have hgt : ∃ x ∈ tf.allDatatypes, (x.name == g) = true ∧ x = d := by
        have := List.find?_some hg; grind [List.mem_of_find?_eq_some, TypeFactory.getType]
      have hgname : d.name = g := by
        rcases hgt with ⟨x, _, hx1, rfl⟩; exact of_decide_eq_true (by simpa using hx1)
      have hmemTF : d.name ∈ tf.allTypeNames := by
        rcases hgt with ⟨x, hxmem, _, rfl⟩
        simp only [TypeFactory.allTypeNames, List.mem_map]
        exact ⟨x, hxmem, rfl⟩
      have hns : g ∉ st.seenTypes := fun h => hskip (Or.inr h)
      have h := seenTypes_add_unseenTypes_lt st tf karities d.name
        (Or.inl hmemTF) (hgname ▸ hns)
      simpa [CollectState.unseenTypes, CollectState.addDatatype, hgname] using h
    · -- addSort branch: `g ∈ karities.map (·.1)` from `find?` success
      refine Prod.Lex.left _ _ ?_
      rename_i s
      have hfind : (fun x : String × Nat => x.1 == g) (s, arity) = true :=
        @List.find?_some (String × Nat) (fun x => x.1 == g) (s, arity) karities hk
      have hmem : (s, arity) ∈ karities := List.mem_of_find?_eq_some hk
      have hs_eq : s = g := by simpa using hfind
      have hgKarity : g ∈ karities.map (·.1) := by
        simp only [List.mem_map]; exact ⟨(s, arity), hmem, hs_eq⟩
      have hns : g ∉ st.seenTypes := fun h => hskip (Or.inr h)
      exact seenTypes_add_unseenTypes_lt st tf karities g (Or.inr hgKarity) hns
    · exact Prod.Lex.right _ (by simp)

/-- Datatype/sort names the resolved-function signatures in `cctx` mention — the second type-seed source
    (besides the expression's own annotations). A type can first appear only in a reachable function's
    argument/return type. `fnDecls` store the collapsed arrow type; `fnDefs` store arg/return types
    separately. -/
def CoreCtx.fnSigTypeRefs (useArrayTheory : Bool) (cctx : CoreCtx) : List String :=
  cctx.fnDecls.flatMap (fun (_, ty) => tyNameRefs useArrayTheory ty) ++
  cctx.fnDefs.flatMap (fun d => d.argTys.flatMap (tyNameRefs useArrayTheory) ++ tyNameRefs useArrayTheory d.retTy)

/-- Accumulate all types (datatypes and opaque sorts) reachable from `e` into `st`, seeding from the
    expression's type annotations and the signatures of functions already resolved in `st.ctx`. Run after
    `collectFuncs` so reachable function signatures participate in the seed. -/
def collectTypes (useArrayTheory : Bool) (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (karities : KnownTypeArities) (st : CollectState) (e : Expression.Expr) : CollectState :=
  collectTypesGo useArrayTheory tf karities st (exprTypeRefs useArrayTheory e ++ st.ctx.fnSigTypeRefs useArrayTheory)

/-- Phase 1 — collect a single expression: extend `st` with the functions and types `e` transitively
    references (functions first, so their signatures seed the type walk). -/
def collect (useArrayTheory : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (karities : KnownTypeArities) (st : CollectState)
    (e : Expression.Expr) : CollectState :=
  collectTypes useArrayTheory tf karities ((collectFuncs useArrayTheory F tf st e).materializeFuncs F) e


/-! ## Phase 1 at the obligation level

`collectObligation` builds one complete `CoreCtx` for a whole `ProofObligation`:
  • flatten the path-condition entries and partition by kind into the program-level chunks —
    `.assumption` → `assumptions`, `.varDecl _ _ (.det e)` → `varDefs`, `.varDecl _ _ .nondet` →
    `varDecls`, `.distinct _ es` → `distincts`;
  • fold the function-reachability `collect` over every expression (assumption bodies, distinct members,
    varDef bodies, and the goal).
The result is a single order-independent `CoreCtx`. -/

/-- Partition a proof obligation's flattened path-condition entries into the program-level `CoreCtx`
    chunks. A `.varDecl` with a non-monomorphic type is dropped here (reported later in the translate
    phase). -/
def CoreCtx.addObligationEntries (cctx : CoreCtx) (d : Imperative.ProofObligation Expression) : CoreCtx :=
  d.assumptions.flatten.foldl (init := cctx) fun c entry =>
    match entry with
    | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
    | .varDecl name ty (.det e) =>
      match ty.toMonoType? with
      | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
      | none => c
    | .varDecl name ty .nondet =>
      match ty.toMonoType? with
      | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
      | none => c
    | .distinct _ es => { c with distincts := c.distincts ++ [es] }

/-- Every expression a proof obligation contributes (for the function-reachability fold): assumption
    bodies, distinct-group members, deterministic varDef bodies, and the goal. -/
def obligationExprs (d : Imperative.ProofObligation Expression) : List Expression.Expr :=
  (d.assumptions.flatten.flatMap fun entry =>
    match entry with
    | .assumption _ e => [e]
    | .varDecl _ _ (.det e) => [e]
    | .varDecl _ _ .nondet => []
    | .distinct _ es => es) ++ [d.obligation]

/-! ### Obligation-level producers — unmanaged free variables and type-constructor arities

Walk the obligation's expressions (and, for arities, the factory) to build the assumed inputs
`SurroundingCtx.fctx` and `KnownTypeArities`. -/

/-- The names an obligation binds within itself (managed vars): every `.varDecl` name, nondet or det.
    Subtracted from the raw free-variable walk when producing the unmanaged fvar context
    (`unmanagedFVars`). -/
def managedNames (d : Imperative.ProofObligation Expression) : List String :=
  d.assumptions.flatten.filterMap fun
    | .varDecl name _ _ => some name.name
    | _ => none

/-- The unmanaged free-variable context of an obligation: fold `LExpr.freeVars` over every obligation
    expression, keep only annotated fvars, and drop those with an in-obligation binding site
    (`managedNames`), deduplicated by name. Returns `(name, type)` pairs. -/
def unmanagedFVars (d : Imperative.ProofObligation Expression) : List (String × LMonoTy) :=
  let managed := managedNames d
  let raw := (obligationExprs d).flatMap Lambda.LExpr.freeVars
  raw.foldl (init := ([] : List (String × LMonoTy))) fun acc (ident, ty?) =>
    match ty? with
    | some ty =>
      if managed.contains ident.name || acc.any (·.1 == ident.name) then acc
      else acc ++ [(ident.name, ty)]
    | none => acc

/-- Type-constructor arities referenced in a monotype: `(name, arg-count)` per `.tcons` head, recursing
    into the arguments. The arity is read off the (consistent) usage. -/
def tyConArities : LMonoTy → List (String × Nat)
  | .tcons name args => (name, args.length) :: args.flatMap tyConArities
  | _ => []

/-- Type-constructor arities referenced in an expression's type annotations. -/
def exprTypeArities : Expression.Expr → List (String × Nat)
  | .op () _ ty         => (ty.map tyConArities).getD []
  | .fvar () _ ty       => (ty.map tyConArities).getD []
  | .app () fn e        => exprTypeArities fn ++ exprTypeArities e
  | .ite () c t e       => exprTypeArities c ++ exprTypeArities t ++ exprTypeArities e
  | .eq () e1 e2        => exprTypeArities e1 ++ exprTypeArities e2
  | .abs () _ ty e      => (ty.map tyConArities).getD [] ++ exprTypeArities e
  | .quant () _ _ ty tr e =>
      (ty.map tyConArities).getD [] ++ exprTypeArities tr ++ exprTypeArities e
  | _                   => []

/-- Type-constructor arities in a function's signature, body, and axioms. -/
def funcTypeArities (f : LFunc CoreLParams) : List (String × Nat) :=
  (f.inputs.toList.flatMap (fun (_, ty) => tyConArities ty)) ++ tyConArities f.output
    ++ (f.body.map exprTypeArities |>.getD []) ++ f.axioms.flatMap exprTypeArities

/-- **Trusted-boundary producer for `KnownTypeArities`.** The arity of every type constructor the
    obligation can reach: walk the obligation's expression type annotations and every factory function's
    signature/body/axioms, collecting `(name, arg-count)` per `.tcons` head, deduped by name. Each arity
    is read off a (consistent) usage, so `Map`, datatypes, and user abstract types are covered uniformly.
    Over-approximates the reachable set — the collect consults an entry only for an opaque sort on a
    `TypeFactory` miss (after the builtin check), so builtin/unused entries are harmless. -/
public def karitiesOf (F : Lambda.Factory CoreLParams) (d : Imperative.ProofObligation Expression) :
    KnownTypeArities :=
  let raw := (obligationExprs d).flatMap exprTypeArities
    ++ F.toArray.toList.flatMap funcTypeArities
  raw.foldl (init := ([] : KnownTypeArities)) fun acc (nm, ar) =>
    if acc.any (·.1 == nm) then acc else acc ++ [(nm, ar)]

/-- Group the reached datatypes (`used`, by name) into their type-factory mutual blocks, in `tf`'s block
    order; each block is filtered to its reached members and empty blocks are dropped. `LDatatype`-level
    (`uAT`-free) — the SMT-shape conversion happens later in `translate`. -/
def datatypeBlocksLD (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (used : List String) :
    List (List (LDatatype CoreLParams.IDMeta)) :=
  tf.toList.filterMap fun block =>
    let usedBlock := block.filter (fun d => used.contains d.name)
    if usedBlock.isEmpty then none else some usedBlock

/-- Phase 1 — collect at the obligation level. Partition the path conditions into the program-level
    chunks, then run the two closures in DAG order:
      1. the function-instance closure (`collectFuncs`) over every obligation expression, so the resolved
         function signatures are available as type seeds;
      2. the type closure (`collectTypes`) over every expression once.
    Yields one complete `CoreCtx`. -/
def collectObligation (useArrayTheory : Bool) (sctx : SurroundingCtx)
    (d : Imperative.ProofObligation Expression) : CoreCtx :=
  let exprs := obligationExprs d
  -- Seed the assumed unmanaged fvars (`sctx.fctx`) at the FRONT of the `varDecls` chunk (the variable
  -- namespace `Φ`), ahead of the obligation's managed nondet vars (from `addObligationEntries`). Both are
  -- `.fvar`-head symbols emitted as `declare-fun`; `materializeFuncs` populates the separate `fnDecls`
  -- (function namespace `Ψ`). Under the lift-pass precondition, no `define-fun` body references a free
  -- var, so `varDecls` may be emitted after `fnDefs`.
  let base0 := CoreCtx.addObligationEntries {} d
  let base := { base0 with varDecls := sctx.fctx ++ base0.varDecls }
  let st : CollectState := { ctx := base }
  let st := exprs.foldl (collectFuncs useArrayTheory sctx.F sctx.tf) st       -- reachable function names
  let st := st.materializeFuncs sctx.F                                        -- materialize decls/defs in factory order
  let st := exprs.foldl (collectTypes useArrayTheory sctx.tf sctx.karities) st -- types, functions now known
  -- Group the reached datatypes (`seenTypes`) into their type-factory mutual blocks, in block order. The
  -- block structure lives only in `tf.toList`; this is the single place the `CoreCtx` reads it, so the
  -- downstream `translate` phase needs no `tf`.
  { st.ctx with datatypes := datatypeBlocksLD sctx.tf st.seenTypes }

/-! ## Phase 2 — `translate`

The translation half: a finished `CoreCtx` → SMT `Term`s / `SMTQuery`. Reads a completed
`CoreCtx`/`TranslateEnv` and never touches `CollectState` or the reachability walk.

Opens with the pure `LMonoTy`→SMT type helpers `collectArrowTy` / `tyToTermType`, used throughout
phase 2 (`translateAppHead`, `sigToSMT`, the binder sort in `translate`).

### Type translation -/

-- `collectArrowTy` is defined in `Expression` (imported above).

/-- Total `LMonoTy → TermType`, datatype-aware. Maps every user datatype `.tcons name args` to the SMT
    sort constructor `.constr name args'` and a type variable to a nullary `.constr tv []`. When
    `useArrayTheory`, `Map k v` → `.constr "Array" [k',v']`; else it stays `.constr "Map" …` (an
    uninterpreted sort). -/
def tyToTermType (useArrayTheory : Bool) : LMonoTy → TermType
  | .bitvec n => .bitvec n
  | .tcons "bool" [] => .bool
  | .tcons "int" [] => .int
  | .tcons "real" [] => .real
  | .tcons "string" [] => .string
  | .tcons "regex" [] => .regex
  | .tcons "Map" args =>
    let id := if useArrayTheory then "Array" else "Map"
    .constr id (args.map (tyToTermType useArrayTheory))
  | .tcons name args => .constr name (args.map (tyToTermType useArrayTheory))
  | .ftvar tv => .constr tv []

/-- The projection of `CoreCtx` that Phase-2 translation reads — the reader environment for
    `translate`/`appTranslate`/`translateAppHead`. Of `CoreCtx`'s chunks, the per-expression recursion
    consults only two:
      • `usedNames` — the static declared-symbol names a fresh quantifier binder must avoid (reachable
        fn/UF names, sort/datatype names, all var decls/defs; `quantUsedNames` unions in the binder stack).
      • `datatypeFuns` — the op-name→(kind, constructor) index `translateAppHead` resolves `.op` heads
        against before the UF fallback.
    Everything else in `CoreCtx` is emitted at the query level and never threaded through the recursion. -/
structure TranslateEnv where
  /-- Static declared-symbol names the binder-freshness search avoids. -/
  usedNames : List String := []
  /-- Datatype-op resolution index, projected from `CoreCtx.datatypeFuns`. -/
  datatypeFuns : Map String (Op.DatatypeFuncs × LConstr CoreLParams.IDMeta) := ∅
  deriving Inhabited

/-- Project the Phase-2 reader environment out of a collected `CoreCtx`. `usedNames` gathers every
    static declared-symbol name; `datatypeFuns` passes through. -/
def CoreCtx.toTranslateEnv (cctx : CoreCtx) : TranslateEnv where
  -- NOTE (datatype extension seam): `usedNames` collects declared FUNCTION/VAR/SORT and datatype TYPE
  -- names, but NOT the datatype-OP names (constructors/selectors/testers — the `datatypeFuns` keys).
  -- Those are emitted symbols too, so a pretty quantifier binder could shadow one; when datatypes enter
  -- the verified subset, append `cctx.datatypeFuns` keys here (freshness) alongside the typing-level
  -- `Ψ ∩ datatype-ops = ∅` disjointness (`FnCtxWF`). Benign today: the verified subset is datatype-free and binders
  -- emit as the reserved `$__bv{depth}` prefix.
  usedNames := cctx.declaredNames
  datatypeFuns := cctx.datatypeFuns

/-- Application-head translation: a predefined operator (via `corePredefinedOpToSMTOp`) applied to the
    accumulated args `acc` at the annotation-derived result sort, else a datatype op (constructor /
    tester / selector, via `tenv.datatypeFuns`), else a free-variable / user-defined-function UF
    application built from the head's arrow annotation. Types are translated via `tyToTermType
    useArrayTheory`. -/
def translateAppHead (useArrayTheory : Bool) (tenv : TranslateEnv) (head : Expression.Expr) (acc : List Term) :
    Except Format Term :=
  match head with
  | .fvar () f (some ty) =>
    let (argTys, rty) := collectArrowTy ty
    let smtRty := tyToTermType useArrayTheory rty
    .ok (.app (.core (.uf ⟨f.name, argTys.map (tyToTermType useArrayTheory), smtRty⟩)) acc smtRty)
  | .op () o (some oty) =>
    let (argTys, rty) := collectArrowTy oty
    -- Classify on the demangled base name: a monomorphized op mangled to `$__mono#base#…` must have
    -- predefined-op / datatype-op recognition key on the base name. `demangledBaseName` is the identity
    -- on unmangled names. The UF fallback keeps the raw (mangled) `o.name` as the SMT id.
    let baseName := Core.NameMangling.demangledBaseName o.name
    -- `re.loop(x, n1, n2)`: indexed regex op — the two Nat bounds are op parameters, not ordinary args.
    -- After spine translation `acc = [regexTerm, (int n1), (int n2)]`; bake the bounds into `Op.re_loop`
    -- and apply it to just the regex term.
    if baseName == "Re.Loop" then
      -- `re.loop`'s two bounds must be non-negative integer literals (they become op parameters). Report
      -- the specific offending bound.
      let loopErr (why : String) : Except Format Term :=
        .error f!"re.loop requires two natural-number literal bounds, but {why}. \
                  (re.loop's repetition counts must be concrete after evaluation; a symbolic or \
                  out-of-range bound cannot be encoded to SMT-LIB.)"
      match acc with
      | [xt, lo, hi] =>
        match lo, hi with
        | .prim (.int n1), .prim (.int n2) =>
          match Int.toNat? n1, Int.toNat? n2 with
          | some n1n, some n2n => .ok (Term.app (Op.re_loop n1n n2n) [xt] .regex)
          | none, _ => loopErr s!"the lower bound {n1} is negative"
          | _, none => loopErr s!"the upper bound {n2} is negative"
        | .prim (.int _), _ => loopErr "the upper bound is not an integer literal (e.g. a quantified or symbolic index)"
        | _, _ => loopErr "the lower bound is not an integer literal (e.g. a quantified or symbolic index)"
      | _ => loopErr s!"got {acc.length} argument(s) instead of 3"
    else
    match corePredefinedOpToSMTOp useArrayTheory (CoreOp.ofString baseName) with
    | some builder => .ok (builder acc (tyToTermType useArrayTheory rty))
    | none =>
      -- Datatype op (constructor / tester / selector)? Resolve via the datatype index before falling
      -- back to a user-function UF. Emit `.datatype_op kind name`, where `name` is the constructor name
      -- for constructors/testers and the safe (stripped) selector name for selectors.
      match tenv.datatypeFuns.find? baseName with
      | some (kind, c) =>
        let name := match kind with
          | .selector => Lambda.stripUnsafeDestructorSuffix baseName
          | _ => c.name.name
        .ok (.app (.datatype_op kind name) acc (tyToTermType useArrayTheory rty))
      | none =>
        let smtRty := tyToTermType useArrayTheory rty
        .ok (.app (.core (.uf ⟨o.name, argTys.map (tyToTermType useArrayTheory), smtRty⟩)) acc smtRty)
  | _ => .error "Unsupported application head"

/-- SMT-LIB identifier sanitization: prefix a leading `@`/`.` with `$` so the name is a legal SMT-LIB
    symbol. -/
def sanitizeSmtName (name : String) : String :=
  if name.isEmpty then name
  else if name.front == '@' || name.front == '.' then "$" ++ name else name

-- Quantifier binder naming. The base name for a quantifier binder is:
--   • the quantifier's `prettyName` when non-empty — a readable base via `Name.breakDisambiguated` +
--     `sanitizeSmtName`;
--   • else `$__bv{bvs.length}` — the binder's de Bruijn depth.
-- The base is then made collision-free within its scope by `Name.findUnique` against the used-name set
-- (enclosing bvs + reachable ufs/fn-names + sorts + datatypes).

/-- The set of names a fresh quantifier binder must avoid at a given point in translation: the enclosing
    bound vars (`bvs`) plus the static declared-symbol names of `tenv` (reachable function/UF names,
    sort/datatype names, and all variable declarations/definitions). Feeding this to `Name.findUnique`
    guarantees the binder cannot capture any free symbol. -/
def quantUsedNames (tenv : TranslateEnv) (bvs : List TermVar) : Std.HashSet String :=
  Std.HashSet.ofList <| bvs.map (·.id) ++ tenv.usedNames

/-- Is `tr` a *structured* Core trigger-list expression — a `Triggers.addGroup`/`Triggers.empty` spine, or
    `LExpr.noTrigger` (a bare `.bvar`)? If not, the caller treats `tr` as a single unstructured pattern
    term. Mirrors production's `SMTEncoder.isCoreTriggerListExpr` (classifies on the demangled base name). -/
def isCoreTriggerListExpr (tr : Expression.Expr) : Bool :=
  match tr with
  | .bvar () _ => true  -- `LExpr.noTrigger`
  | .op () opId _ =>
    match CoreOp.ofString (Core.NameMangling.demangledBaseName opId.name) with
    | .trigger .EmptyTriggers | .trigger .EmptyGroup => true
    | _ => false
  | .app () (.app () (.op () opId _) _) _ =>
    match CoreOp.ofString (Core.NameMangling.demangledBaseName opId.name) with
    | .trigger .AddGroup => true
    | _ => false
  | _ => false

mutual
/-- Phase 2 — pure Core→SMT translation of an expression: constants, `.bvar` (via `bvs`), `.ite`/`.eq`,
    `.quant`, and fvar/UDF/op heads as UF or predefined-op applications (via `corePredefinedOpToSMTOp`).
    Quantifier binders are named depth-based (`$__bv{bvs.length}` when the pretty name is empty, else the
    readable pretty name), disambiguated by `Name.findUnique`. -/
def translate (useArrayTheory : Bool) (tenv : TranslateEnv)
    (bvs : List TermVar) (e : Expression.Expr) : Except Format Term :=
  match e with
  | .const () c =>
    match c with
    | .boolConst b => .ok (.prim (.bool b))
    | .intConst i => .ok (.prim (.int i))
    | .bitvecConst _ b => .ok (.prim (.bitvec b))
    | .strConst s => .ok (.prim (.string s))
    | .realConst r =>
      -- Exact decimal if `r` has a terminating expansion, else `(/ num den)`.
      match StrataDDM.Decimal.fromRat r with
      | some d => .ok (Term.real d)
      | none =>
        let num := Term.real (StrataDDM.Decimal.ofInt r.num)
        let den := Term.real (StrataDDM.Decimal.ofInt (Int.ofNat r.den))
        .ok (Term.app Op.rdiv [num, den] .real)
  | .bvar () i =>
    if h : i < bvs.length then .ok (.var bvs[i])
    else .error f!"Bound variable index out of bounds: {i}"
  | .ite () c t e_ => do
    let ct ← translate useArrayTheory tenv bvs c
    let tt ← translate useArrayTheory tenv bvs t
    let et ← translate useArrayTheory tenv bvs e_
    -- Use `Factory.ite`/`Factory.eq` (not raw `Term.app`) for the constant/reflexivity simplifications
    -- (e.g. `t = t` ↦ `true`).
    .ok (Factory.ite ct tt et)
  | .eq () e1 e2 => do
    let t1 ← translate useArrayTheory tenv bvs e1
    let t2 ← translate useArrayTheory tenv bvs e2
    .ok (Factory.eq t1 t2)
  | .quant () k pretty (some qty) tr body => do
    -- Base name: the user-provided readable name when present, else a depth-based `$__bv{depth}`
    -- (`depth = bvs.length`). `findUnique` resolves any residual clash against the names in scope.
    let (baseName, startSuffix) :=
      if pretty.isEmpty then (s!"$__bv{bvs.length}", 1)
      else let (b, s) := Strata.Name.breakDisambiguated pretty; (sanitizeSmtName b, s)
    let name := Strata.Name.findUnique baseName startSuffix (quantUsedNames tenv bvs)
    let v : TermVar := ⟨name, tyToTermType useArrayTheory qty⟩
    -- Lower the trigger under the extended binder ctx into `List (List Term)` `:pattern` groups
    -- (`Term.quant` carries triggers as `List (List Term)` directly). A structured
    -- `Triggers.*` spine is decomposed by `translateTriggerGroups`; any other expression is a single
    -- unstructured pattern term forming one group. Denotation ignores triggers; they only guide solver
    -- instantiation. Mirrors production `SMTEncoder`'s `.quant` case.
    let trBvs := v :: bvs
    let trGroups ←
      if isCoreTriggerListExpr tr then
        translateTriggerGroups useArrayTheory tenv trBvs tr []
      else do
        let tt ← translate useArrayTheory tenv trBvs tr
        .ok [[tt]]
    let bodyTm ← translate useArrayTheory tenv trBvs body
    -- Use `Factory.quant` (not raw `.quant`) for nested-quantifier coalescing + simple-trigger
    -- (bare-bvar = no-op) handling.
    let smtKind : Strata.SMT.QuantifierKind := match k with
      | .all => .all | .exist => .exist
    .ok (Factory.quant smtKind v.id v.ty trGroups bodyTm)
  | .op () o oty =>
    -- 0-ary operation (bare `.op` not under `.app`): dispatch via `translateAppHead` with empty args.
    translateAppHead useArrayTheory tenv (.op () o oty) []
  | .fvar () f (some ty) =>
    translateAppHead useArrayTheory tenv (.fvar () f (some ty)) []
  | .app () fn arg => do
    let argt ← translate useArrayTheory tenv bvs arg
    appTranslate useArrayTheory tenv bvs fn [argt]
  | _ => .error "Unsupported expression form"

/-- Peel an application spine, translating each argument (under `bvs`) eagerly onto `acc`, then dispatch
    the head via `translateAppHead`. -/
def appTranslate (useArrayTheory : Bool) (tenv : TranslateEnv)
    (bvs : List TermVar) (head : Expression.Expr) (acc : List Term) : Except Format Term :=
  match head with
  | .app () fn arg => do
    let argt ← translate useArrayTheory tenv bvs arg
    appTranslate useArrayTheory tenv bvs fn (argt :: acc)
  | h => translateAppHead useArrayTheory tenv h acc

/-- Decompose one Core trigger *group* — a `TriggerGroup.addTrigger` spine ending in `TriggerGroup.empty`
    — into its encoded SMT pattern terms, each translated under the (binder-extended) `bvs`. Accumulator
    prepended (matching production `SMTEncoder.encodeTriggerGroup`). -/
def translateTriggerGroup (useArrayTheory : Bool) (tenv : TranslateEnv) (bvs : List TermVar)
    (g : Expression.Expr) (acc : List Term) : Except Format (List Term) :=
  match g with
  | .op () _ _ => .ok acc  -- `TriggerGroup.empty`: end of the group spine.
  | .app () (.app () (.op () opId _) t) rest =>
    match CoreOp.ofString (Core.NameMangling.demangledBaseName opId.name) with
    | .trigger .AddTrigger => do
      let tt ← translate useArrayTheory tenv bvs t
      translateTriggerGroup useArrayTheory tenv bvs rest (tt :: acc)
    | _ => .error f!"Unexpected operator in trigger group: {opId.name}"
  | _ => .error f!"Unexpected trigger group expression"

/-- Decompose a structured Core trigger LExpr — a `Triggers.addGroup` spine ending in `Triggers.empty`, or
    `LExpr.noTrigger` (a bare `.bvar`) — into SMT `:pattern` groups. Accumulator prepended (matching
    production `SMTEncoder.encodeTriggerGroups`), so groups come out in reverse spine order — identical to
    production, hence byte-compatible. -/
def translateTriggerGroups (useArrayTheory : Bool) (tenv : TranslateEnv) (bvs : List TermVar)
    (tr : Expression.Expr) (acc : List (List Term)) : Except Format (List (List Term)) :=
  match tr with
  | .bvar () _ => .ok acc  -- `LExpr.noTrigger`: no meaningful trigger.
  | .op () _ _ => .ok acc  -- `Triggers.empty`: end of the group-list spine.
  | .app () (.app () (.op () opId _) g) rest =>
    match CoreOp.ofString (Core.NameMangling.demangledBaseName opId.name) with
    | .trigger .AddGroup => do
      let group ← translateTriggerGroup useArrayTheory tenv bvs g []
      translateTriggerGroups useArrayTheory tenv bvs rest (group :: acc)
    | _ => .error f!"Unexpected operator in trigger list: {opId.name}"
  | _ => .error f!"Unexpected trigger expression"
end

/-! ## Phase 2 at the obligation level: translate the whole `CoreCtx`

Turn a fully-collected `CoreCtx` + the obligation goal into the SMT query components, sourced from the
by-kind chunks and translated against the one shared `CoreCtx`. -/

-- `RConstructor` and `SMTQuery` (`DenoteTypedSMTQuery`) are defined in the language files (imported above).

/-- Translate a Core-level signature `(argTys, retTy)` to SMT `(List TermType × TermType)` via
    `tyToTermType useArrayTheory`. -/
def sigToSMT (useArrayTheory : Bool) (argTys : List LMonoTy) (retTy : LMonoTy) :
    List TermType × TermType :=
  (argTys.map (tyToTermType useArrayTheory), tyToTermType useArrayTheory retTy)

/-- The SMT binder list for a function definition's `define-fun`: each source formal `(name, ty)` becomes
    a `TermVar ⟨name, tyToTermType ty⟩`, in order. -/
def fnDefSmtParams (useArrayTheory : Bool) (d : FnDef) : List TermVar :=
  d.params.map (fun (n, ty) => ⟨n, tyToTermType useArrayTheory ty⟩)

/-- Turn a resolved datatype into its `declare-datatype` triple `(name, typeArgs, constructors)`: each
    constructor keeps its bare name, and each field is `(Datatype..field, sort)` with the field sort via
    `tyToTermType` (a `.ftvar` type parameter becomes the nullary `.constr tv []`). -/
def datatypeDeclOf (useArrayTheory : Bool) (d : LDatatype CoreLParams.IDMeta) :
    String × List String × List RConstructor :=
  let constrs := d.constrs.map fun c =>
    let fields := c.args.map fun (fname, fty) => (d.name ++ ".." ++ fname.name, tyToTermType useArrayTheory fty)
    ({ name := c.name.name, args := fields } : RConstructor)
  (d.name, d.typeArgs, constrs)

/-- Translate a list of expressions, each under the empty binder ctx, into their SMT terms. A plain
    `mapM` — the elements are independent (binder names are depth-based). -/
def translateList (useArrayTheory : Bool) (tenv : TranslateEnv)
    (es : List Expression.Expr) : Except Format (List Term) :=
  es.mapM (fun e => translate useArrayTheory tenv [] e)

/-- Phase 2 — assemble the SMT query from a collected `CoreCtx` + goal. Every expression is translated
    against the same `cctx`; the chunks become the corresponding SMT declaration (`IF`/`UF`) / assertion
    lists. Quantifier binder names are depth-based, so each chunk translates independently. -/
def translateQuery (useArrayTheory : Bool)
    (cctx : CoreCtx) (goal : Expression.Expr) :
    Except Format SMTQuery := do
  -- Project the narrow Phase-2 reader environment once; the recursion sees only `tenv` (used-names +
  -- datatypeFuns), never the full `cctx`. The chunk-emission below still reads `cctx` directly.
  let tenv := cctx.toTranslateEnv
  -- interpreted functions (IF): parameters are named by the source formal names, and the body is
  -- translated under exactly those binders so its `.bvar` occurrences resolve positionally to `IF.args`.
  let fnDefs ← cctx.fnDefs.mapM fun d => do
    let params : List TermVar := fnDefSmtParams useArrayTheory d
    let smtRet := tyToTermType useArrayTheory d.retTy
    let bodyTm ← translate useArrayTheory tenv params d.body
    .ok ({ id := d.name, args := params, out := smtRet, body := bodyTm } : IF)
  -- uninterpreted functions (UF): the reachable uninterpreted factory functions (`fnDecls`). Decompose
  -- the (possibly arrow) type via `collectArrowTy`: an arrow-typed decl becomes an n-ary UF, a base-typed
  -- one a nullary UF. Emitted before `fnDefs`.
  let fnDecls := cctx.fnDecls.map fun (name, ty) =>
    let (smtArgs, smtRet) := sigToSMT useArrayTheory (collectArrowTy ty).1 (collectArrowTy ty).2
    ({ id := name, args := smtArgs, out := smtRet } : UF)
  -- variable definitions (nullary IF) and declarations (nullary UF)
  let varDefs ← cctx.varDefs.mapM fun v => do
    let bodyTm ← translate useArrayTheory tenv [] v.body
    .ok ({ id := v.name, args := [], out := tyToTermType useArrayTheory v.ty, body := bodyTm } : IF)
  -- variable declarations (UF): the variable namespace `Φ` (free vars + nondet program vars). Decompose
  -- the (possibly arrow) type via `collectArrowTy` — a higher-order free var becomes an n-ary UF, an
  -- ordinary base-typed program var a nullary UF (byte-identical to the old nullary-only emission).
  let varDecls := cctx.varDecls.map fun (name, ty) =>
    let (smtArgs, smtRet) := sigToSMT useArrayTheory (collectArrowTy ty).1 (collectArrowTy ty).2
    ({ id := name, args := smtArgs, out := smtRet } : UF)
  -- assertion terms (each translated independently; depth-based binder naming)
  let fnAxioms ← translateList useArrayTheory tenv cctx.fnAxioms
  let assumptionTerms ← translateList useArrayTheory tenv cctx.assumptions
  let distinctTerms ← cctx.distincts.mapM fun es => do
    let ts ← translateList useArrayTheory tenv es
    .ok (Term.app (.core .distinct) ts .bool)
  let obl ← translate useArrayTheory tenv [] goal
  -- user datatype declarations (declare-datatype[s]): each collected mutual block, SMT-shape-converted;
  -- the block structure is read straight from `cctx.datatypes`
  let datatypes := cctx.datatypes.map (·.map (datatypeDeclOf useArrayTheory))
  -- opaque sorts (declare-sort): name + arity, straight from the collected `sorts` chunk
  let sorts := cctx.sorts.map fun (name, arity) => ({ name, arity } : Strata.DL.SMT.Sort)
  -- distinct assertions are folded into `assumptions` (both become assertion terms)
  .ok { datatypes, sorts, fnDecls := fnDecls, fnDefs := fnDefs, fnAxioms,
        varDecls, varDefs,
        assumptions := assumptionTerms ++ distinctTerms, obl }

/-- End-to-end obligation encoder: `collectObligation` then `translateQuery`. Collect one complete
    `CoreCtx` from the whole obligation (closed over the assumed free-variable context `fctx`), then
    translate every chunk into the SMT query components. `fctx` is an assumed input (the fourth
    surrounding context, alongside `F`/`tf`/`karities`). -/
def encodeObligation (useArrayTheory : Bool) (sctx : SurroundingCtx)
    (d : Imperative.ProofObligation Expression) : Except Format SMTQuery :=
  translateQuery useArrayTheory (collectObligation useArrayTheory sctx d) d.obligation

/-- Runtime entry point: instantiates the assumed `fctx` with the trusted producer `unmanagedFVars d`.
    The caller supplies the closing function/type/sort contexts (`F`/`tf`/`karities`); `fctx` is filled
    in from the obligation. -/
public def encodeObligationRun (useArrayTheory : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (karities : KnownTypeArities)
    (d : Imperative.ProofObligation Expression) : Except Format SMTQuery :=
  encodeObligation useArrayTheory ⟨F, tf, karities, unmanagedFVars d⟩ d

end Core.Refactor
