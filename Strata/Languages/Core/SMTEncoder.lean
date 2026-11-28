/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DL.Lambda.LTyProps

public import Strata.DL.Imperative.PathConditionsFold
public import Strata.DL.Imperative.SMTUtils
public import Strata.DL.SMT.Factory
public import Strata.DL.SMT.DenoteDatatypes
public import Strata.Languages.Core.Env
public import Strata.Util.Name
public import Strata.Util.OrderedSet
public import Strata.Util.Statistics
public import Strata.Languages.Core.NameMangling
public import Strata.DL.SMT.DDMTransform.Translate -- shake: keep
public import Strata.Util.PtrCache
import Strata.Util.Worklist
import Strata.Languages.Core.Statistics
import Strata.Util.Tactics

---------------------------------------------------------------------

namespace Core
open Std (ToFormat Format format)
open Lambda Strata.SMT Strata.SMT.Encoder
open Strata.Util (OrderedSet OrderedKeyedSet)
open Imperative (PathConditionEntry ExprOrNondet PathCondition PathConditions)
open Imperative.PathConditions (Fold FoldState)

public section

/-- Location of expressions this file builds itself. -/
abbrev smtEncodingLoc : ExprSourceLoc := ExprSourceLoc.synthesized "smt-encoding"

/-- Location of expressions decoded from an SMT model. -/
abbrev smtModelLoc : ExprSourceLoc := ExprSourceLoc.synthesized "smt-model"
/--
A factory function whose UF declaration has been emitted but whose
definition (interpreted body and/or axioms) has not been encoded as SMT.Term yet.

`fn`/`fnty` are the call-site identifier and function type. -/
structure SMT.PendingFnDef where
  fn : CoreIdent
  uf : UF
  fnty : LMonoTy
deriving Repr, Inhabited

/--
An insertion-ordered, `uf`-deduplicated queue of `PendingFnDef`s. -/
abbrev SMT.PendingFnQueue : Type := OrderedKeyedSet ((·.uf) : SMT.PendingFnDef → UF)

/--
A factory function whose body and axioms have been encoded to SMT `Term`s,
ready to be committed to the `SMT.Context`.
-/
structure SMT.EncodedFnDef where
  id : String
  args : List TermVar
  out : TermType
  body? : Option Term
  axioms : List Term
  /-- `body?` is a recursive definition to be emitted as `define-fun-rec`. -/
  isRec : Bool := false
deriving Repr, Inhabited

/--
The encoder's datatype registry: the env's `TypeFactory` (kept in topological,
mutual-block order for emission) paired with a name→datatype index for O(1)
lookup during encoding.
-/
structure SMT.Datatypes where
  private mk ::
  factory : @Lambda.TypeFactory CoreLParams.IDMeta
  private index : Std.HashMap String (LDatatype CoreLParams.IDMeta)
deriving Repr, Inhabited

/-- Build a `Datatypes` from a `TypeFactory`, computing the name index in one
    pass. -/
def SMT.Datatypes.ofFactory (tf : @Lambda.TypeFactory CoreLParams.IDMeta) : SMT.Datatypes :=
  .mk tf (tf.allDatatypes.foldl (fun m d => m.insertIfNew d.name d) {})

/-- The empty registry (no datatypes). -/
def SMT.Datatypes.empty : SMT.Datatypes := .ofFactory #[]

/-- Lookup a datatype by name. -/
def SMT.Datatypes.getType (d : SMT.Datatypes) (name : String) :
    Option (LDatatype CoreLParams.IDMeta) :=
  d.index.get? name

/--
SMT.Context holds the list of created SMT sorts, declared/defined functions, axioms,
type substitutions and others while translating Imperative.ProofObligation Expression to
SMT. This is one of the objects in an `EncodeResult` (see `encodeObligationToSMT`).

SMT.Context also has fields that are invariant during translation; they are
explicitly marked as invariant in their comments.
-/
structure SMT.Context where
  /-- Declared SMT sorts, plus uninterpreted functions, defined functions, and
  axioms. Each keeps insertion order for emit while deduplicating in O(1) via a
  built-in membership index (the array and index cannot drift apart). -/
  sorts : OrderedSet Strata.DL.SMT.Sort := .empty
  ufs : OrderedSet UF := .empty
  ifs : OrderedKeyedSet IF.toUF := .empty
  axms : OrderedSet Term := .empty
  /-- Unused by the encoder (all input is monomorphic); retained for type
      compatibility with shared utilities. -/
  tySubst: Map String TermType := []
  /-- The known datatypes: the `TypeFactory` (kept in topological order for
  emission) together with a name→datatype index for O(1) lookup. Seeded by the
  caller (from the env's datatype factory) before encoding, via
  `SMT.Datatypes.ofFactory`/`withTypeFactory`, and not modified afterwards — it
  holds *all* known datatypes, including ones never referenced by the encoded
  terms; `seenDatatypes` records which of them are actually used. -/
  datatypes : SMT.Datatypes := .empty
  seenDatatypes : Std.HashSet String := {}
  datatypeFuns : Std.HashMap String (Op.DatatypeFuncs × LConstr CoreLParams.IDMeta) := {}
  /-- When true, encode `Map` types/operations using the SMT Array theory
      (`select`/`store`) instead of an uninterpreted `Map` sort.
      Invariant during translation. -/
  useArrayTheory : Bool := false
  /-- When true, a recursive function with a body is encoded as a
      `define-fun-rec` definition instead of an uninterpreted function with
      per-constructor axioms (`VerifyOptions.recursiveFnsAsDefineFunRec`).
      Invariant during translation. -/
  recFnsAsDefineFunRec : Bool := false
deriving Repr, Inhabited

def SMT.Context.default : SMT.Context := {}

/-- Sort names that cvc5 or z3 already define. A `declare-sort` or `declare-datatype` of one
    of them is not a fresh sort: z3 rejects it, and cvc5 can silently keep its own sort, with
    that sort's equality and cardinality (cvc5's `Array`, `Nullable`, `Set` and `Tuple` do
    this), so the solver could prove facts that do not hold for Strata's uninterpreted sort.
    `Scripts/scan_solver_sort_names.sh` checks this list against the solver binaries; re-run
    it whenever cvc5 or z3 is upgraded. -/
def solverBuiltinSortNames : Std.HashSet String := .ofList
  ["Array", "Bag", "BitVec", "Bool", "FiniteField", "Float128", "Float16", "Float32",
   "Float64", "FloatingPoint", "Int", "List", "Nullable", "Real", "RegEx", "RegLan",
   "Relation", "RoundingMode", "Seq", "Set", "String", "StringSequence", "Table", "Tuple",
   "Unicode", "UnitTuple", "bv",
   -- Symbols cvc5 rejects as a sort name.
   "abs", "as", "let", "match", "par", "select", "store"]

/-- Prefix that `smtSortName` adds to a sort name. -/
@[expose] def smtSortPrefix : String := "$__Strata_"

/-- The SMT-LIB name of the Core sort, datatype or datatype type parameter `id`: `id`
    with `smtSortPrefix` when the solvers already define a sort of that name or when `id`
    itself starts with `smtSortPrefix`, and `id` otherwise. Prefixing the names that
    already carry the prefix keeps the mapping injective: a user type named
    `$__Strata_Set` becomes `$__Strata_$__Strata_Set`, not Core's `Set`. -/
def smtSortName (id : String) : String :=
  if solverBuiltinSortNames.contains id || id.startsWith smtSortPrefix then smtSortPrefix ++ id
  else id

/-- The Core name of the SMT-LIB sort name `name`; the inverse of `smtSortName`. -/
def coreSortName (name : String) : String :=
  if name.startsWith smtSortPrefix then (name.drop smtSortPrefix.length).toString else name

/-- The run of consecutive copies of `p` that starts `cs`: how many, and what follows. -/
private def prefixRun (p : List Char) : Nat → List Char → Nat × List Char
  | 0, cs => (0, cs)
  | fuel + 1, cs =>
    if !p.isEmpty && p.isPrefixOf cs then
      let (k, rest) := prefixRun p fuel (cs.drop p.length)
      (k + 1, rest)
    else (0, cs)

private def coreSortNamesInAux (p : List Char) : Nat → Option Char → List Char → List Char
  | 0, _, cs => cs
  | fuel + 1, prev, cs =>
    -- `smtSortName` adds the prefix at the start of a name, so only a prefix there counts:
    -- at the start of the string, or after a delimiter of the solvers' value syntax.
    let atNameStart := prev.all (· ∈ ['(', ' ', '|', '@'])
    if atNameStart && !p.isEmpty && p.isPrefixOf cs then
      let (k, rest) := prefixRun p (cs.length + 1) cs
      (List.replicate (k - 1) p).flatten ++ coreSortNamesInAux p fuel (some '_') rest
    else
      match cs with
      | [] => []
      | c :: cs' => c :: coreSortNamesInAux p fuel (some c) cs'

/-- `s` with every SMT-LIB sort name in it mapped back by `coreSortName`. A solver names its
    abstract values after their sort (cvc5's `@($__Strata_Set Int)_0`, z3's
    `$__Strata_Set!val!0`); this shows them under the Core name (`@(Set Int)_0`). As
    `coreSortName` does for one name, it drops one `smtSortPrefix` from each run of
    consecutive prefixes that starts a name. -/
def coreSortNamesIn (s : String) : String :=
  String.ofList (coreSortNamesInAux smtSortPrefix.toList (s.length + 1) none s.toList)

/-- A model value name with the sort names in it mapped back by `coreSortNamesIn`, if it is
    an abstract value the solver made up (cvc5's `@(…)_n`, z3's `…!val!n`); any other
    name, such as a user's, as it is. -/
def coreValueName (id : String) : String :=
  if id.startsWith "@" || (id.splitOn "!val!").length > 1 then coreSortNamesIn id else id

def SMT.Context.addSort (ctx : SMT.Context) (sort : Strata.DL.SMT.Sort) : SMT.Context :=
  { ctx with sorts := ctx.sorts.insert sort }

def SMT.Context.addUF (ctx : SMT.Context) (fn : UF) : SMT.Context :=
  { ctx with ufs := ctx.ufs.insert fn }

def SMT.Context.addIF (ctx : SMT.Context) (id : String) (args : List TermVar) (out : TermType) (body : Term)
    (isRec : Bool := false) : SMT.Context :=
  { ctx with ifs := ctx.ifs.insert { id, args, out, body, isRec } }

def SMT.Context.addAxiom (ctx : SMT.Context) (axm : Term) : SMT.Context :=
  { ctx with axms := ctx.axms.insert axm }

/-- Commit a resolved function definition: emit its interpreted body (`addIF`)
    or uninterpreted declaration (`addUF`), followed by its axioms (`addAxiom`). -/
def SMT.Context.addResolvedFnDef (ctx : SMT.Context) (rdef : SMT.EncodedFnDef) : SMT.Context :=
  let ctx := match rdef.body? with
    | some body =>
      ctx.addIF rdef.id rdef.args rdef.out body rdef.isRec
    | none =>
      let uf : UF := { id := rdef.id, args := rdef.args.map (·.ty), out := rdef.out }
      ctx.addUF uf
  rdef.axioms.foldl (init := ctx) (·.addAxiom ·)

/-- True if the function `uf`'s declaration has already been committed: it is
    in `ufs` (uninterpreted) or `ifs` (interpreted). -/
def SMT.Context.committedFn (ctx : SMT.Context) (uf : UF) : Bool :=
  ctx.ufs.contains uf || ctx.ifs.containsKey uf

def SMT.Context.hasDatatype (ctx : SMT.Context) (name : String) : Bool :=
  ctx.seenDatatypes.contains name

/-- Asserts the encoder invariant that all input is monomorphic. -/
def SMT.Context.checkMonomorphic (ctx : SMT.Context) : Except Format Unit :=
  if ctx.tySubst.isEmpty then .ok ()
  else .error f!"SMT encoding: non-empty tySubst reached the encoder \
                 ({ctx.tySubst.length} entries) — the input should be fully \
                 monomorphic post-`MonomorphizeFunctions`."

/-- Collect all sort, datatype, constructor, and selector names that have been
    pre-declared to the solver. Used to pre-populate the encoder's `usedNames`
    registry so that later UF/function encoding cannot collide with them. -/
def SMT.Context.preDeclaredNames (ctx : SMT.Context) : Std.HashSet String :=
  let sortNames := ctx.sorts.toArray.foldl (init := ({} : Std.HashSet String)) fun acc s => acc.insert s.name
  let dtNames := ctx.datatypes.factory.toList.foldl (init := sortNames) fun acc block =>
    block.foldl (init := acc) fun acc d =>
      if ctx.seenDatatypes.contains d.name then
        let acc := acc.insert (smtSortName d.name)
        -- Include constructor and selector names emitted by declareDatatype
        d.constrs.foldl (init := acc) fun acc c =>
          let acc := acc.insert c.name.name
          c.args.foldl (init := acc) fun acc (fieldName, _) =>
            acc.insert (Lambda.destructorFuncName d fieldName)
      else acc
  -- Built-in Option datatype names
  let acc := dtNames.insert "Option"
  let acc := acc.insert "none"
  let acc := acc.insert "some"
  acc.insert "val"

def SMT.Context.addDatatype (ctx : SMT.Context) (d : LDatatype CoreLParams.IDMeta) : SMT.Context :=
  if ctx.hasDatatype d.name then ctx
  else
    let (c, i, s, u) := d.genFunctionMaps
    -- First binding for a name wins (matching `Map.union` semantics), hence `insertIfNew`.
    let insertNew := fun (m : Std.HashMap String (Op.DatatypeFuncs × LConstr CoreLParams.IDMeta))
        (kind : Op.DatatypeFuncs) (entries : Map String (LDatatype CoreLParams.IDMeta × LConstr CoreLParams.IDMeta)) =>
      entries.toList.foldl (fun m (name, _, c) => m.insertIfNew name (kind, c)) m
    let m := insertNew ctx.datatypeFuns .constructor c
    let m := insertNew m .tester i
    let m := insertNew m .selector s
    let m := insertNew m .selector u
    { ctx with seenDatatypes := ctx.seenDatatypes.insert d.name, datatypeFuns := m }

def SMT.Context.withTypeFactory (ctx : SMT.Context) (tf : @Lambda.TypeFactory CoreLParams.IDMeta) : SMT.Context :=
  { ctx with datatypes := .ofFactory tf }

/--
Helper function to convert LMonoTy to TermType for datatype constructor fields.
Handles monomorphic types and type variables (as `.constr tv []`).
-/
def lMonoTyToTermType (useArrayTheory : Bool := false) (ty : LMonoTy) : TermType :=
  match ty with
  | .bitvec n => .bitvec n
  | .tcons "bool" [] => .bool
  | .tcons "int" [] => .int
  | .tcons "real" [] => .real
  | .tcons "string" [] => .string
  | .tcons "regex" [] => .regex
  | .tcons "Set" [elem] =>
    -- A set is its characteristic function: `Set τ` is the SMT array `Array τ Bool`.
    if useArrayTheory then
      .constr "Array" [lMonoTyToTermType useArrayTheory elem, .bool]
    else
      .constr (smtSortName "Set") [lMonoTyToTermType useArrayTheory elem]
  -- A function value is total and extensional, as is an SMT array.
  | .tcons "arrow" [dom, cod] =>
    .constr "Array" [lMonoTyToTermType useArrayTheory dom, lMonoTyToTermType useArrayTheory cod]
  | .tcons name args =>
    if name == "Map" && useArrayTheory then
      .constr "Array" (args.map $ lMonoTyToTermType useArrayTheory)
    else
      .constr (smtSortName name) (args.map $ lMonoTyToTermType useArrayTheory)
  | .ftvar tv => .constr (smtSortName tv) []

/-- Convert a datatype's constructors to typed SMT constructors: the one place that names
    constructors and selectors and lowers field types, for every solver interface. -/
def datatypeConstructorsToSMT (d : LDatatype CoreLParams.IDMeta) (useArrayTheory : Bool := false)
    : List SMTConstructor :=
  d.constrs.map fun c =>
    let fields := c.args.map fun (name, fieldTy) =>
      (Lambda.destructorFuncName d name, lMonoTyToTermType useArrayTheory fieldTy)
    { name := c.name.name, args := fields }

/-- The datatypes a query uses, as `Strata.DL.SMT.Denote` declares them: name and
    constructors with selector symbols and field sorts, in factory order. `none` if a
    used datatype is parametric, which the denotation does not cover. -/
def SMT.Context.denotedDatatypes (ctx : SMT.Context) : Option Strata.SMT.DT.Decls := do
  let mut out : Array (String × List SMTConstructor) := #[]
  for block in ctx.datatypes.factory.toList do
    for d in block do
      if ctx.seenDatatypes.contains d.name then
        if !d.typeArgs.isEmpty then failure
        out := out.push (d.name, datatypeConstructorsToSMT d ctx.useArrayTheory)
  return out.toList

/-- Does a datatype of `names` occur in the argument or the result of a function
    type within `ty`? Such a datatype, e.g. `Tree { Node(kids: int -> Tree) }` or
    `Tree { Node(f: Tree -> int) }`, recurses through an SMT array, which cvc5
    rejects as a nested-recursive datatype and z3 as not co-variant. -/
def recursesThroughFunction (names : List String) : LMonoTy → Bool
  | .tcons "arrow" [dom, cod] =>
    (Lambda.getTypeRefs dom ++ Lambda.getTypeRefs cod).any (names.contains ·) ||
      recursesThroughFunction names dom || recursesThroughFunction names cod
  | .tcons _ args => args.attach.any fun x => recursesThroughFunction names x.1
  | _ => false
termination_by ty => sizeOf ty
decreasing_by all_goals (try cases x); all_goals (simp_wf; try omega); all_goals term_by_mem

/-- Is `ty` a function type? -/
def isFunctionType : LMonoTy → Bool
  | .tcons "arrow" [_, _] => true
  | _ => false

/-- Is `ty` a map or a set, an SMT array under array theory? -/
def isMapOrSet : LMonoTy → Bool
  | .tcons "Map" [_, _] | .tcons "Set" [_] => true
  | _ => false

/-- Does `ty` contain an array sort indexed by an array sort: a function whose argument is a
    function, and under array theory a function whose argument is a map or a set, a map
    keyed by a function or a set of functions? Its
    SMT sort is an array indexed by an array, which cvc5 rejects. A map or a set keyed by a
    map or a set is left alone: programs with one verify today. -/
def hasArrayIndexedByArray (useArrayTheory : Bool) : LMonoTy → Bool
  | .tcons "arrow" [dom, cod] =>
    isFunctionType dom || (useArrayTheory && isMapOrSet dom) ||
      hasArrayIndexedByArray useArrayTheory dom ||
      hasArrayIndexedByArray useArrayTheory cod
  | .tcons "Map" [k, v] =>
    (useArrayTheory && isFunctionType k) || hasArrayIndexedByArray useArrayTheory k ||
      hasArrayIndexedByArray useArrayTheory v
  | .tcons "Set" [e] =>
    (useArrayTheory && isFunctionType e) || hasArrayIndexedByArray useArrayTheory e
  | .tcons _ args => args.attach.any fun x => hasArrayIndexedByArray useArrayTheory x.1
  | _ => false
termination_by ty => sizeOf ty
decreasing_by all_goals (try cases x); all_goals (simp_wf; try omega); all_goals term_by_mem

/-- Ensures that no datatype in the SMT encoding recurses through the argument or
    the result of a function-typed constructor argument. -/
def validateDatatypesForSMT (typeFactory : @Lambda.TypeFactory CoreLParams.IDMeta)
    (seenDatatypes : Std.HashSet String) (useArrayTheory : Bool := false) :
    Except Format Unit := do
  for block in typeFactory.toList do
    let names := block.map (·.name)
    for d in block do
      if !seenDatatypes.contains d.name then continue
      for c in d.constrs do
        for (fieldName, fieldTy) in c.args do
          if recursesThroughFunction names fieldTy then
            throw f!"Cannot encode datatype '{d.name}' to SMT: \
                     constructor '{c.name.name}' has field '{fieldName.name}' of type \
                     '{fieldTy}', which recurses through a function type."
          if hasArrayIndexedByArray useArrayTheory fieldTy then
            throw f!"Cannot encode datatype '{d.name}' to SMT: \
                     constructor '{c.name.name}' has field '{fieldName.name}' of type \
                     '{fieldTy}', whose SMT sort is an array indexed by an array, which \
                     cvc5 rejects."

/--
Emit datatype declarations to the solver.
Uses the TypeFactory ordering (already topologically sorted).
Only emits datatypes that have been seen (added via addDatatype).
Single-element blocks use declare-datatype, multi-element blocks use declare-datatypes.
-/
def SMT.Context.emitDatatypes (ctx : SMT.Context) : Strata.SMT.SolverEncodingM Unit := do
  match validateDatatypesForSMT ctx.datatypes.factory ctx.seenDatatypes ctx.useArrayTheory with
  | .error msg => throw (IO.userError (toString msg))
  | .ok () => pure ()
  for block in ctx.datatypes.factory.toList do
    let usedBlock := block.filter (fun d => ctx.seenDatatypes.contains d.name)
    match usedBlock with
    | [] => pure ()
    | [d] =>
      let constructors := datatypeConstructorsToSMT d ctx.useArrayTheory
      Strata.SMT.Solver.declareDatatype (smtSortName d.name) (d.typeArgs.map smtSortName)
        constructors
    | _ =>
      let dts := usedBlock.map fun d =>
        (smtSortName d.name, d.typeArgs.map smtSortName,
          datatypeConstructorsToSMT d ctx.useArrayTheory)
      Strata.SMT.Solver.declareDatatypes dts

/-- Emit a context's sort declarations, then its datatype declarations (whose
    constructors may mention the sorts). -/
def SMT.writeSortsAndDatatypes (ctx : SMT.Context) : Strata.SMT.SolverEncodingM Unit := do
  let _ ← ctx.sorts.toArray.mapM fun s => Strata.SMT.Solver.declareSort s.name s.arity
  ctx.emitDatatypes

abbrev BoundVars := List (String × TermType)

---------------------------------------------------------------------
/--
Returns true if the given type name is a built-in Core type whose SMT-LIB
encoding is handled specially and should not be declared via `declare-sort`.
-/
def isBuiltinCoreTy (id : String) : Bool :=
  id ∈ ["bool", "int", "real", "string", "regex"]

/-
Add a type to the context. Sorts are easy, but datatypes are tricky:
we must also ensure we add the types of all arguments in the constructors
to the context, recursively. This is very tricky to prove terminating, so
we leave as `partial` for now.
-/
partial def SMT.Context.addType (id: String) (args: List LMonoTy) (ctx: SMT.Context) :
  SMT.Context :=
  -- Always recurse into concrete args to register any type references
  let ctx := args.foldl (fun ctx arg =>
    match arg with
    | .tcons id1 args1 =>
      if isBuiltinCoreTy id1 then ctx
      else SMT.Context.addType id1 args1 ctx
    | _ => ctx) ctx
  -- Already registered: its constructors were recursed when first added, so
  -- there is nothing to do. `seenDatatypes` only ever holds factory datatype
  -- names (its sole writer is `addDatatype`, called below on a `getType`
  -- result), so this branch fires only for factory datatypes (emitted as
  -- declare-datatype), never for the opaque sorts (declare-sort) the `none`
  -- branch handles.
  if ctx.hasDatatype id then ctx
  -- A function type is the native SMT array sort; only its argument types
  -- (registered above) need declaring.
  else if id == "arrow" then ctx
  else match ctx.datatypes.getType id with
  | some d =>
    let ctx := ctx.addDatatype d
    d.constrs.foldl (fun (ctx : SMT.Context) c =>
      c.args.foldl (fun (ctx: SMT.Context) (_, t) =>
        match t with
        | .bool | .int | .real | .string | .tcons "regex" [] => ctx
        | .tcons id1 args1 => SMT.Context.addType id1 args1 ctx
        | _ => ctx
        ) ctx
      ) ctx
  | none =>
    ctx.addSort { name := smtSortName id, arity := args.length }

mutual
/-- The error for a type whose SMT sort is an array indexed by an array. With
    `arrayTheory`, the array comes from array theory and the message says to run without
    it. -/
def arrayIndexedByArrayError (ty : LMonoTy) (arrayTheory : Bool := false) : Format :=
  let hint := if arrayTheory then "; run without --use-array-theory" else ""
  f!"Cannot encode the type '{ty}' to SMT: its sort is an array indexed by an array, \
    which cvc5 rejects{hint}."

def LMonoTy.toSMTType (ty : LMonoTy) (ctx : SMT.Context) :
  Except Format (TermType × SMT.Context) := do
  match ty with
  | .bitvec n => .ok (.bitvec n, ctx)
  | .tcons "bool" [] => .ok (.bool, ctx)
  | .tcons "int"  [] => .ok (.int, ctx)
  | .tcons "real" [] => .ok (.real, ctx)
  | .tcons "string"  [] => .ok (.string, ctx)
  | .tcons "regex" [] => .ok (.regex, ctx)
  | .tcons "Map" args =>
    if hasArrayIndexedByArray ctx.useArrayTheory ty then
      throw (arrayIndexedByArrayError ty (!hasArrayIndexedByArray false ty))
    -- When using Array theory, convert Map to Array
    let id := if ctx.useArrayTheory then "Array" else "Map"
    let ctx := if ctx.useArrayTheory then ctx
               else SMT.Context.addType id args ctx
    let (args', ctx) ← LMonoTys.toSMTType args ctx
    -- `id` is `Array` (the theory's own sort) or `Map`, which no solver defines.
    .ok ((.constr id args'), ctx)
  | .tcons "Set" [elem] =>
    if hasArrayIndexedByArray ctx.useArrayTheory ty then
      throw (arrayIndexedByArrayError ty (!hasArrayIndexedByArray false ty))
    -- Under array theory the sort is native, so it needs no `declare-sort` (and gains
    -- extensionality: two sets with equal membership are the same term). Without array
    -- theory it stays an uninterpreted sort constrained by the `Set.*` axioms.
    if ctx.useArrayTheory then
      let (elem', ctx) ← LMonoTy.toSMTType elem ctx
      .ok (.constr "Array" [elem', .bool], ctx)
    else
      let ctx := SMT.Context.addType "Set" [elem] ctx
      let (elem', ctx) ← LMonoTy.toSMTType elem ctx
      .ok (.constr (smtSortName "Set") [elem'], ctx)
  | .tcons "arrow" [dom, cod] =>
    if isFunctionType dom then
      throw (arrayIndexedByArrayError ty)
    if ctx.useArrayTheory && isMapOrSet dom then
      throw (arrayIndexedByArrayError ty true)
    let (dom', ctx) ← LMonoTy.toSMTType dom ctx
    let (cod', ctx) ← LMonoTy.toSMTType cod ctx
    .ok (.constr "Array" [dom', cod'], ctx)
  | .tcons id args =>
    let ctx := SMT.Context.addType id args ctx
    let (args', ctx) ← LMonoTys.toSMTType args ctx
    .ok ((.constr (smtSortName id) args'), ctx)
  | .ftvar tyv =>
    -- If the encoder sees a type variable, that's a bug — either
    -- MonomorphizeFunctions failed to reach this reference, or something
    -- re-introduced polymorphism.
    .error f!"SMT encoding: unexpected type variable '{tyv}' — \
              the input to SMTEncoder should be fully monomorphic."

def LMonoTys.toSMTType (args : LMonoTys) (ctx : SMT.Context) :
    Except Format ((List TermType) × SMT.Context) := do
  match args with
  | [] => .ok ([], ctx)
  | t :: trest =>
    let (t', ctx) ← LMonoTy.toSMTType t ctx
    let (trest', ctx) ← LMonoTys.toSMTType trest ctx
    .ok ((t' :: trest'), ctx)
end

def convertQuantifierKind : Lambda.QuantifierKind -> Strata.SMT.QuantifierKind
  | .all => .all
  | .exist => .exist

/--
Encode a Core *predefined* operator (Booleans, arithmetic, bitvectors,
strings, regexes, triggers, and the overflow predicates) to the
corresponding SMT operator builder.
-/
def corePredefinedOpToSMTOp (op : CoreOp) (ctx : SMT.Context) :
    Option ((List Term → TermType → Term) × TermType × SMT.Context) :=
  match op with
  | .bool .And     => some (.app Op.and,        .bool,   ctx)
  | .bool .Or      => some (.app Op.or,         .bool,   ctx)
  | .bool .Not     => some (.app Op.not,        .bool,   ctx)
  | .bool .Implies => some (.app Op.implies,    .bool,   ctx)
  | .bool .Equiv   => some (.app Op.eq,         .bool,   ctx)

  | .numeric ⟨.int, .Neg⟩      => some (.app Op.neg,        .int ,   ctx)
  | .numeric ⟨.int, .Add⟩      => some (.app Op.add,        .int ,   ctx)
  | .numeric ⟨.int, .Sub⟩      => some (.app Op.sub,        .int ,   ctx)
  | .numeric ⟨.int, .Mul⟩      => some (.app Op.mul,        .int ,   ctx)
  | .numeric ⟨.int, .Div⟩ | .numeric ⟨.int, .SafeDiv⟩ =>
    -- Safe to encode as normal SMT div/mod: preconditions have already been
    -- checked and generated well-formedness conditions in the environment.
    some (.app Op.div,        .int ,   ctx)
  | .numeric ⟨.int, .Mod⟩ | .numeric ⟨.int, .SafeMod⟩ =>
    some (.app Op.mod,        .int ,   ctx)
  -- Truncating division: tdiv(a,b) = let q = ediv(abs(a), abs(b)) in ite(a*b >= 0, q, -q)
  | .numeric ⟨.int, .DivT⟩ | .numeric ⟨.int, .SafeDivT⟩ =>
    let divTApp := fun (args : List Term) (retTy : TermType) =>
      match args with
      | [a, b] =>
        let zero := Term.prim (.int 0)
        let ab := Term.app Op.mul [a, b] retTy
        let abGeZero := Term.app Op.ge [ab, zero] .bool
        let absA := Term.app Op.abs [a] retTy
        let absB := Term.app Op.abs [b] retTy
        let q := Term.app Op.div [absA, absB] retTy
        let negQ := Term.app Op.neg [q] retTy
        Factory.ite abGeZero q negQ
      | _ => Term.app Op.div args retTy
    some (divTApp, .int, ctx)
  -- Truncating modulo: tmod(a,b) = a - b * tdiv(a,b)
  -- tdiv(a,b) = let q = ediv(abs(a), abs(b)) in ite(a*b >= 0, q, -q)
  | .numeric ⟨.int, .ModT⟩ | .numeric ⟨.int, .SafeModT⟩ =>
    let modTApp := fun (args : List Term) (retTy : TermType) =>
      match args with
      | [a, b] =>
        let zero := Term.prim (.int 0)
        let ab := Term.app Op.mul [a, b] retTy
        let abGeZero := Term.app Op.ge [ab, zero] .bool
        let absA := Term.app Op.abs [a] retTy
        let absB := Term.app Op.abs [b] retTy
        let q := Term.app Op.div [absA, absB] retTy
        let negQ := Term.app Op.neg [q] retTy
        let tdivAB := Term.app Op.ite [abGeZero, q, negQ] retTy
        let bTimesTdiv := Term.app Op.mul [b, tdivAB] retTy
        Term.app Op.sub [a, bTimesTdiv] retTy
      | _ => Term.app Op.mod args retTy
    some (modTApp, .int, ctx)
  | .numeric ⟨.int, .Lt⟩       => some (.app Op.lt,         .bool,   ctx)
  | .numeric ⟨.int, .Le⟩       => some (.app Op.le,         .bool,   ctx)
  | .numeric ⟨.int, .Gt⟩       => some (.app Op.gt,         .bool,   ctx)
  | .numeric ⟨.int, .Ge⟩       => some (.app Op.ge,         .bool,   ctx)

  | .numeric ⟨.real, .Neg⟩     => some (.app Op.neg,        .real,   ctx)
  | .numeric ⟨.real, .Add⟩     => some (.app Op.add,        .real,   ctx)
  | .numeric ⟨.real, .Sub⟩     => some (.app Op.sub,        .real,   ctx)
  | .numeric ⟨.real, .Mul⟩     => some (.app Op.mul,        .real,   ctx)
  | .numeric ⟨.real, .Div⟩     => some (.app Op.rdiv,       .real,   ctx)
  | .numeric ⟨.real, .Lt⟩      => some (.app Op.lt,         .bool,   ctx)
  | .numeric ⟨.real, .Le⟩      => some (.app Op.le,         .bool,   ctx)
  | .numeric ⟨.real, .Gt⟩      => some (.app Op.gt,         .bool,   ctx)
  | .numeric ⟨.real, .Ge⟩      => some (.app Op.ge,         .bool,   ctx)

  -- Bitvector operations: size-generic via CoreOp
  | .bv ⟨n, .Neg⟩  => some (.app Op.bvneg,      .bitvec n, ctx)
  | .bv ⟨n, .Add⟩  => some (.app Op.bvadd,      .bitvec n, ctx)
  | .bv ⟨n, .Sub⟩  => some (.app Op.bvsub,      .bitvec n, ctx)
  | .bv ⟨n, .Mul⟩  => some (.app Op.bvmul,      .bitvec n, ctx)
  | .bv ⟨n, .UDiv⟩ => some (.app Op.bvudiv,     .bitvec n, ctx)
  | .bv ⟨n, .UMod⟩ => some (.app Op.bvurem,     .bitvec n, ctx)
  | .bv ⟨n, .SDiv⟩ => some (.app Op.bvsdiv,     .bitvec n, ctx)
  | .bv ⟨n, .SMod⟩ => some (.app Op.bvsrem,     .bitvec n, ctx)
  | .bv ⟨n, .Not⟩  => some (.app Op.bvnot,      .bitvec n, ctx)
  | .bv ⟨n, .And⟩  => some (.app Op.bvand,      .bitvec n, ctx)
  | .bv ⟨n, .Or⟩   => some (.app Op.bvor,       .bitvec n, ctx)
  | .bv ⟨n, .Xor⟩  => some (.app Op.bvxor,      .bitvec n, ctx)
  | .bv ⟨n, .Shl⟩  => some (.app Op.bvshl,      .bitvec n, ctx)
  | .bv ⟨n, .UShr⟩ => some (.app Op.bvlshr,     .bitvec n, ctx)
  | .bv ⟨n, .SShr⟩ => some (.app Op.bvashr,     .bitvec n, ctx)
  | .bv ⟨_, .ULt⟩  => some (.app Op.bvult,      .bool,   ctx)
  | .bv ⟨_, .ULe⟩  => some (.app Op.bvule,      .bool,   ctx)
  | .bv ⟨_, .UGt⟩  => some (.app Op.bvugt,      .bool,   ctx)
  | .bv ⟨_, .UGe⟩  => some (.app Op.bvuge,      .bool,   ctx)
  | .bv ⟨_, .SLt⟩  => some (.app Op.bvslt,      .bool,   ctx)
  | .bv ⟨_, .SLe⟩  => some (.app Op.bvsle,      .bool,   ctx)
  | .bv ⟨_, .SGt⟩  => some (.app Op.bvsgt,      .bool,   ctx)
  | .bv ⟨_, .SGe⟩  => some (.app Op.bvsge,      .bool,   ctx)
  | .bv ⟨n, .Concat⟩ => some (.app Op.bvconcat,    .bitvec (n * 2), ctx)
  | .bv ⟨_, .ToUInt⟩  => some (.app Op.ubv_to_int,  .int,            ctx)
  | .bv ⟨_, .ToInt⟩   => some (.app Op.sbv_to_int,  .int,            ctx)
  | .intToBv n        => some (.app (Op.int_to_bv n), .bitvec n,     ctx)

  | .str .Length   => some (.app Op.str_length,    .int,    ctx)
  | .str .Concat   => some (.app Op.str_concat,    .string, ctx)
  | .str .Substr   => some (.app Op.str_substr,    .string, ctx)
  | .str .ToRegEx  => some (.app Op.str_to_re,     .regex,  ctx)
  | .str .InRegEx  => some (.app Op.str_in_re,     .bool,   ctx)
  | .str .PrefixOf => some (.app Op.str_prefixof,  .bool,   ctx)
  | .str .SuffixOf => some (.app Op.str_suffixof,  .bool,   ctx)
  | .str .Contains => some (.app Op.str_contains,  .bool,   ctx)
  | .str .IndexOf  => some (.app Op.str_indexof,   .int,    ctx)
  | .str .Replace  => some (.app Op.str_replace,   .string, ctx)
  | .str .At       => some (.app Op.str_at,        .string, ctx)
  | .str .Lt       => some (.app Op.str_lt,        .bool,   ctx)
  | .str .Le       => some (.app Op.str_le,        .bool,   ctx)
  | .str .ToCode   => some (.app Op.str_to_code,   .int,    ctx)
  | .str .FromCode => some (.app Op.str_from_code, .string, ctx)
  | .str .FromInt  => some (.app Op.str_from_int,  .string, ctx)
  | .str .ToInt    => some (.app Op.str_to_int,    .int,    ctx)
  | .re .All       => some (.app Op.re_all,        .regex,  ctx)
  | .re .AllChar   => some (.app Op.re_allchar,    .regex,  ctx)
  | .re .Range     => some (.app Op.re_range,      .regex,  ctx)
  | .re .Concat    => some (.app Op.re_concat,     .regex,  ctx)
  | .re .Star      => some (.app Op.re_star,       .regex,  ctx)
  | .re .Plus      => some (.app Op.re_plus,       .regex,  ctx)
  | .re .Union     => some (.app Op.re_union,      .regex,  ctx)
  | .re .Inter     => some (.app Op.re_inter,      .regex,  ctx)
  | .re .Comp      => some (.app Op.re_comp,       .regex,  ctx)
  | .re .None      => some (.app Op.re_none,       .regex,  ctx)

  -- Note: Core `Triggers`/`TriggerGroup` operators are not lowered here; they are
  -- handled structurally by `encodeTriggerGroups` in the `.quant` case.

  -- Safe BV operations: same encoding as unsafe (preconditions already checked)
  | .bv ⟨n, .SafeAdd⟩ => some (.app Op.bvadd, .bitvec n, ctx)
  | .bv ⟨n, .SafeSub⟩ => some (.app Op.bvsub, .bitvec n, ctx)
  | .bv ⟨n, .SafeMul⟩ => some (.app Op.bvmul, .bitvec n, ctx)
  | .bv ⟨n, .SafeNeg⟩ => some (.app Op.bvneg, .bitvec n, ctx)
  | .bv ⟨n, .SafeUAdd⟩ => some (.app Op.bvadd, .bitvec n, ctx)
  | .bv ⟨n, .SafeUSub⟩ => some (.app Op.bvsub, .bitvec n, ctx)
  | .bv ⟨n, .SafeUMul⟩ => some (.app Op.bvmul, .bitvec n, ctx)
  | .bv ⟨n, .SafeUNeg⟩ => some (.app Op.bvneg, .bitvec n, ctx)
  | .bv ⟨n, .SafeSDiv⟩ => some (.app Op.bvsdiv, .bitvec n, ctx)
  | .bv ⟨n, .SafeSMod⟩ => some (.app Op.bvsrem, .bitvec n, ctx)
  -- Signed overflow predicates
  | .bv ⟨_, .SAddOverflow⟩ => some (.app Op.bvsaddo, .bool, ctx)
  | .bv ⟨_, .SSubOverflow⟩ => some (.app Op.bvssubo, .bool, ctx)
  | .bv ⟨_, .SMulOverflow⟩ => some (.app Op.bvsmulo, .bool, ctx)
  | .bv ⟨_, .SNegOverflow⟩ => some (.app Op.bvnego, .bool, ctx)
  -- SDivOverflow(x, y) = (x == INT_MIN) ∧ (y == -1)
  | .bv ⟨n, .SDivOverflow⟩ =>
    let app := fun (args : List Term) (_retTy : TermType) =>
      match args with
      | [x, y] =>
        let intMin := Term.prim (.bitvec (BitVec.intMin n))
        let negOne := Term.prim (.bitvec (BitVec.allOnes n))
        let xIsMin := Term.app Op.eq [x, intMin] .bool
        let yIsNegOne := Term.app Op.eq [y, negOne] .bool
        Term.app Op.and [xIsMin, yIsNegOne] .bool
      | _ => Term.app Op.and [] .bool
    some (app, .bool, ctx)
  -- Unsigned overflow predicates
  -- UAddOverflow(x, y) = bvult(bvadd(x, y), x) — wrapping add < operand means overflow
  | .bv ⟨_, .UAddOverflow⟩ =>
    let app := fun (args : List Term) (_retTy : TermType) =>
      match args with
      | [x, y] =>
        let bvTy := x.typeOf
        let sum := Term.app Op.bvadd [x, y] bvTy
        Term.app Op.bvult [sum, x] .bool
      | _ => Term.app Op.and [] .bool
    some (app, .bool, ctx)
  | .bv ⟨_, .USubOverflow⟩ => some (Term.app Op.bvult, .bool, ctx)
  -- UMulOverflow(x, y) = bvugt(zero_extend(N, x) * zero_extend(N, y), zero_extend(N, MAX))
  | .bv ⟨n, .UMulOverflow⟩ =>
    let app := fun (args : List Term) (_retTy : TermType) =>
      match args with
      | [x, y] =>
        let extTy := TermType.prim (.bitvec (n + n))
        let xe := Term.app (.zero_extend n) [x] extTy
        let ye := Term.app (.zero_extend n) [y] extTy
        let prod := Term.app Op.bvmul [xe, ye] extTy
        let maxVal := Term.prim (.bitvec (BitVec.allOnes n))
        let maxExt := Term.app (.zero_extend n) [maxVal] extTy
        Term.app Op.bvugt [prod, maxExt] .bool
      | _ => Term.app Op.and [] .bool
    some (app, .bool, ctx)
  -- UNegOverflow(x) = x != 0
  | .bv ⟨n, .UNegOverflow⟩ =>
    let app := fun (args : List Term) (_retTy : TermType) =>
      match args with
      | [x] =>
        let zero := Term.prim (.bitvec (BitVec.zero n))
        Term.app Op.not [Term.app Op.eq [x, zero] .bool] .bool
      | _ => Term.app Op.and [] .bool
    some (app, .bool, ctx)

  | _ => none

/-- The name `fn` is encoded as: for a monomorphized copy, the function its factory entry's
    mark records (`FuncAttr.monoCopyOf`), not one read off its name; otherwise `fn` itself.
    A copy that lost its mark is encoded as an uninterpreted function: weaker, never
    unsound. -/
def SMT.encodedOpName (factory : @Lambda.Factory CoreLParams) (fn : CoreIdent) : String :=
  ((factory[fn.name]?).bind (Strata.DL.Util.FuncAttr.findMonoCopyOf ·.attr)).getD fn.name

/-- The number of arguments the SMT encoding of operator `fn` takes. Arguments
    beyond it are applications of the function value it returns, encoded as
    array `select`s. Datatype constructors take one argument per field, testers
    and selectors take one; other operators take their declared inputs. -/
def SMT.Context.opArity (factory : @Lambda.Factory CoreLParams) (ctx : SMT.Context)
    (fn : CoreIdent) (fnty : LMonoTy) : Nat :=
  match ctx.datatypeFuns.get? (SMT.encodedOpName factory fn) with
  | some (.constructor, c) => c.args.length
  | some _ => 1
  | none =>
    match factory[fn.name]? with
    | some func => func.inputs.length
    | none => (LMonoTy.destructArrow fnty).length - 1

/-- Resolve a Core operator `fn` (of monomorphic type `fnty`) to its SMT builder.

    Returns the updated `SMT.Context` and pending-definition queue `pending`:
    for a user-defined factory function this only registers the `UF` and
    *schedules* a `PendingFnDef` (deferring body/axiom encoding); the queue is
    threaded through term encoding and drained later by `processPendingFnDefs`. -/
def toSMTOp (factory : @Lambda.Factory CoreLParams) (fn : CoreIdent) (fnty : LMonoTy) (ctx : SMT.Context)
  (pending : SMT.PendingFnQueue) :
  Except Format ((List Term → TermType → Term) × TermType × SMT.Context × SMT.PendingFnQueue) :=
  open LTy.Syntax in do
  -- Encode the type to ensure any datatypes are registered in the context
  let tys := LMonoTy.destructArrow fnty
  let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
  let intys := tys.take (tys.length - 1)
  -- Need to encode arg types also (e.g. for testers)
  let ctx := match LMonoTys.toSMTType intys ctx with
    | .ok (_, ctx') => ctx'
    | .error _ => ctx
  let (_, ctx) ← LMonoTy.toSMTType outty ctx
  -- The result after the operator's own arguments, which is a function value
  -- (an SMT array) when the operator returns one, e.g. a function-typed field.
  let (intys, outty) := LMonoTy.splitArrows (ctx.opArity factory fn fnty) fnty
  let (smt_outty, ctx) ← LMonoTy.toSMTType outty ctx

  let baseFn := SMT.encodedOpName factory fn
  match ctx.datatypeFuns.get? baseFn with
  | some (kind, c) =>
    let adtApp := fun (args : List Term) (retty : TermType) =>
        /-
        Note: testers use constructor, translated in `Op.mkName` to is-foo
        Selectors use full function name (Datatype..fieldName) for uniqueness.
        Unsafe selectors (e.g. List..head!) use the safe name (List..head).
        -/
        let name := match kind with
          | .selector => stripUnsafeDestructorSuffix baseFn
          | _ => c.name.name
        Term.app (.datatype_op kind name) args retty
    .ok (adtApp, smt_outty, ctx, pending)
  | none =>
    -- Not a constructor, tester, or destructor
    match factory[fn.name]? with
    | none => .error f!"Cannot find function {fn} in Strata Core's Factory!"
    | some func =>
      -- Built-in dispatch keys on the function a copy specializes (see above).
      let baseName := baseFn
      match corePredefinedOpToSMTOp (CoreOp.ofString baseName) ctx with
      | some (op, retty, ctx) => .ok (op, retty, ctx, pending)
      | none => do
      if (baseName == "select" || baseName == "update") && ctx.useArrayTheory then
        .ok (.app (if baseName == "select" then Op.select else Op.store), smt_outty, ctx, pending)
      -- The three membership-level set operations are exactly array operations on the
      -- characteristic function, so they go straight to the theory instead of being declared
      -- and axiomatized. `insert`/`remove` take two arguments where `store` takes three, so
      -- the stored boolean is appended here.
      --
      -- The axioms for `Set.empty` and the binary operations reference `Set.contains`, which
      -- also routes here, so they remain consistent with the native encoding.
      else if baseName == "Set.contains" && ctx.useArrayTheory then
        .ok (.app Op.select, smt_outty, ctx, pending)
      else if (baseName == "Set.insert" || baseName == "Set.remove") && ctx.useArrayTheory then
        let stored := Term.bool (baseName == "Set.insert")
        .ok ((fun args ty => .app Op.store (args ++ [stored]) ty), smt_outty, ctx, pending)
      else
        let formals := func.inputs.keys
        let formalStrs := formals.map (toString ∘ format)
        let (intys, outty) := LMonoTy.splitArrows func.inputs.length fnty
        let (smt_intys, ctx) ← LMonoTys.toSMTType intys ctx
        let bvs := formalStrs.zip smt_intys
        let (smt_outty, ctx) ← LMonoTy.toSMTType outty ctx
        let uf : UF := { id := (toString $ format fn), args := smt_intys, out := smt_outty }
        -- Lambda redexes (let-alias bindings such as Core's `have`; see
        -- `Strata/Transform/BetaReduce.lean`) are contracted by the
        -- `betaReduce` pipeline phase, and every other abstraction is lifted
        -- by `lambdaLift`, before encoding, so an abstraction here means a
        -- pipeline that skipped those phases.
        if func.body.any LExpr.hasAbs then
          .error f!"Cannot encode function '{func.name}' to SMT: \
                    its body contains a lambda expression. \
                    Lambda abstractions cannot be encoded to SMT. \
                    Consider marking the function as `inline`."
        else
          -- Defer encoding the function's definition (interpreted body and/or
          -- axioms). Those would require calling `toSMTTerm` on expressions
          -- drawn from the factory; schedule a `PendingFnDef` instead. Skip
          -- functions already committed.
          let pending := if ctx.committedFn uf then pending
            else pending.insert { fn := fn, uf := uf, fnty := fnty }
          .ok (.app (Op.uf uf), smt_outty, ctx, pending)

/-- Does `tr` denote a *structured* Core trigger list (a `Triggers.empty` /
    `Triggers.addGroup` spine, or `LExpr.noTrigger`)? If not, the trigger is a bare
    pattern term supplied directly and forms a single `:pattern` group. The trigger operators
    are matched by name: `MonomorphizeFunctions` never copies them (`isTriggerMetaOp`). -/
def isCoreTriggerListExpr (tr : LExpr CoreLParams.mono) : Bool :=
  match tr with
  | .bvar _ _ => true  -- LExpr.noTrigger
  | .op _ opId _ =>
    match CoreOp.ofString opId.name with
    | .trigger .EmptyTriggers | .trigger .EmptyGroup => true
    | _ => false
  | .app _ (.app _ (.op _ opId _) _) _ =>
    match CoreOp.ofString opId.name with
    | .trigger .AddGroup => true
    | _ => false
  | _ => false

/-- The function of `factory` that implements the built-in collection operator `base` at type
    instantiation `tys`: `base` itself, or, once functions are monomorphized, its specialized
    copy. Fails if neither is in the factory: the literal's operator has no copy at `tys`. -/
def collectionOpIdent (factory : @Lambda.Factory CoreLParams) (base : String)
    (tys : List LMonoTy) : Except Format CoreIdent :=
  if (factory[base]?).isSome then .ok ⟨base, ()⟩
  else
    -- The mark (`FuncAttr.monoCopyOf`) decides that a function is `base`'s copy; it does not
    -- record the instantiation, so the copy at `tys` is picked out by the name monomorphization
    -- built for it (`copyName`), under the prefix it chose. No name is decoded here.
    let isCopy (f : Lambda.LFunc CoreLParams) :=
      Strata.DL.Util.FuncAttr.findMonoCopyOf f.attr == some base
    let plain := Core.NameMangling.copyName Core.NameMangling.monoPrefix base tys
    -- Under a padded prefix: the marked copy whose name is the copy's name at `tys` under
    -- its own prefix.
    let scan (_ : Unit) : Except Format CoreIdent :=
      let atTys (n : String) := (Core.NameMangling.copyPrefixOf? n).any fun pfx =>
        n == Core.NameMangling.copyName pfx base tys
      match factory.toArray.find? fun f => isCopy f && atTys f.name.name with
      | some f => .ok f.name
      | none => .error f!"collection literal: the factory has no copy of {base} marked at {tys}"
    match factory[plain]? with
    | some f => if isCopy f then .ok f.name else scan ()
    | none => scan ()

/-- Apply the function value `f` (an SMT array) to `args`, one `select` each. -/
def selectAll (f : Term) (args : List Term) : Term :=
  args.foldl (init := f) fun t a =>
    let codTy := match t.typeOf with
      | .constr "Array" [_, cod] => cod
      | ty => ty
    Term.app Op.select [t, a] codTy

/-- The uninterpreted function a free variable `f` of type `ty` denotes, with
    the argument types it takes: none for a first-order variable, every arrow
    argument for a function-typed one, which is applied as an SMT function. -/
def fvarToUF (f : CoreIdent) (ty : LMonoTy) (ctx : SMT.Context) :
    Except Format (UF × SMT.Context) := do
  let id := if (LMonoTy.destructArrow ty).length == 1 then f.name else toString (format f)
  if hasArrayIndexedByArray ctx.useArrayTheory ty then
    -- Its array sort would be indexed by an array, which cvc5 rejects: it is an
    -- uninterpreted function of its arguments instead, which can only be applied.
    let tys := LMonoTy.destructArrow ty
    let (smtIntys, ctx) ← LMonoTys.toSMTType tys.dropLast ctx
    let (smtOut, ctx) ← LMonoTy.toSMTType (tys.getLastD ty) ctx
    return ({ id, args := smtIntys, out := smtOut }, ctx)
  -- A function-typed free variable is one constant of its array sort: applied, partly or
  -- fully, it is `select`ed, and unapplied it is that array. So it needs no defining
  -- axiom, and a query that compares two of them has only arrays to reason about.
  let (smtTy, ctx) ← LMonoTy.toSMTType ty ctx
  return ({ id, args := [], out := smtTy }, ctx)

/-- Is `e` a free variable whose function value is an opaque constant (`fvarToUF`), or a
    conditional with such a branch? Decided from the types, without encoding `e`. -/
def hasOpaqueFunctionValue (useArrayTheory : Bool) : LExpr CoreLParams.mono → Bool
  | .fvar _ _ (some ty) => isFunctionType ty && hasArrayIndexedByArray useArrayTheory ty
  | .ite _ _ t f => hasOpaqueFunctionValue useArrayTheory t ||
      hasOpaqueFunctionValue useArrayTheory f
  | _ => false

/-- Encode operator `fn` used as a function value, i.e. not applied to the
    arguments `intys` it takes. `op` builds its application and `retty` is the
    type of that application. The value is a constant array `$__fn#<fn>`
    (`Core.NameMangling.fnValuePrefix`) that an axiom makes agree with `fn` at every
    argument. -/
def functionValueToSMT (fn : CoreIdent) (intys : LMonoTys) (op : List Term → TermType → Term)
    (retty : TermType) (ctx : SMT.Context) : Except Format (Term × SMT.Context) := do
  let (smtIntys, ctx) ← LMonoTys.toSMTType intys ctx
  let arrTy := smtIntys.foldr (fun dom cod => .constr "Array" [dom, cod]) retty
  let id := s!"{Core.NameMangling.fnValuePrefix}{Core.NameMangling.monoDelim}{toString $ format fn}"
  let uf : UF := { id, args := [], out := arrTy }
  let fnVal := Term.app (.uf uf) [] arrTy
  if ctx.ufs.contains uf then return (fnVal, ctx)
  let vars := smtIntys.mapIdx fun i ty => ({ id := s!"$__x{i}", ty } : TermVar)
  let varTerms := vars.map Term.var
  let lhs := selectAll fnVal varTerms
  let axm := Term.quant .all vars [[lhs]] (Factory.eq lhs (op varTerms retty))
  return (fnVal, (ctx.addUF uf).addAxiom axm)

mutual
/-- Encode a constant. A collection literal is encoded as the applications of the operators
    that build it (see `Core.litToOpExpr`): `mapConst` and `update` for a map, the first entry
    outermost, and `Sequence.empty` and `Sequence.build` for a sequence. -/
def litToSMTTerm (factory : @Lambda.Factory CoreLParams) (c : LConst) (ctx : SMT.Context)
    (pending : SMT.PendingFnQueue) :
    Except Format (Term × SMT.Context × SMT.PendingFnQueue) :=
  match c with
  | .boolConst b => .ok (Term.bool b, ctx, pending)
  | .intConst i => .ok (Term.int i, ctx, pending)
  | .rationalConst r =>
    match StrataDDM.Decimal.fromRat r with
    | some d => .ok (Term.real d, ctx, pending)
    | none =>
      -- `r` has no terminating decimal expansion (e.g. `1/3`), so encode it as
      -- the exact real division `(/ num den)` rather than erroring.
      let num := Term.real (StrataDDM.Decimal.ofInt r.num)
      let den := Term.real (StrataDDM.Decimal.ofInt (Int.ofNat r.den))
      .ok (.app Op.rdiv [num, den] .real, ctx, pending)
  | .bitvecConst _ b => .ok (Term.bitvec b, ctx, pending)
  | .strConst s => .ok (Term.string s, ctx, pending)
  | .mapConst k v d ⟨xs⟩ => do
    let kt := k.toMonoTy
    let vt := v.toMonoTy
    let (dT, ctx, pending) ← litToSMTTerm factory d ctx pending
    let (mk, mty, ctx, pending) ←
      toSMTOp factory (← collectionOpIdent factory "mapConst" [kt, vt])
        (.arrow vt (mapTy kt vt)) ctx pending
    litEntriesToSMTTerm factory kt vt (mk [dT] mty) xs ctx pending
  | .sequenceConst a ⟨xs⟩ => do
    let et := a.toMonoTy
    let (mk, sty, ctx, pending) ←
      toSMTOp factory (← collectionOpIdent factory "Sequence.empty" [et]) (seqTy et) ctx pending
    litElemsToSMTTerm factory et (mk [] sty) xs ctx pending
/-- Encode `base` updated with map entries, the first one outermost. -/
def litEntriesToSMTTerm (factory : @Lambda.Factory CoreLParams) (kt vt : LMonoTy) (base : Term) :
    List (LConst × LConst) → SMT.Context → SMT.PendingFnQueue →
    Except Format (Term × SMT.Context × SMT.PendingFnQueue)
  | [], ctx, pending => .ok (base, ctx, pending)
  | (key, x) :: rest, ctx, pending => do
    let (restT, ctx, pending) ← litEntriesToSMTTerm factory kt vt base rest ctx pending
    let (keyT, ctx, pending) ← litToSMTTerm factory key ctx pending
    let (xT, ctx, pending) ← litToSMTTerm factory x ctx pending
    let (upd, uty, ctx, pending) ←
      toSMTOp factory (← collectionOpIdent factory "update" [kt, vt])
        (.arrow (mapTy kt vt) (.arrow kt (.arrow vt (mapTy kt vt)))) ctx pending
    .ok (upd [restT, keyT, xT] uty, ctx, pending)
/-- Encode `acc` with sequence elements appended in order. -/
def litElemsToSMTTerm (factory : @Lambda.Factory CoreLParams) (et : LMonoTy) (acc : Term) :
    List LConst → SMT.Context → SMT.PendingFnQueue →
    Except Format (Term × SMT.Context × SMT.PendingFnQueue)
  | [], ctx, pending => .ok (acc, ctx, pending)
  | x :: rest, ctx, pending => do
    let (xT, ctx, pending) ← litToSMTTerm factory x ctx pending
    let (bld, bty, ctx, pending) ←
      toSMTOp factory (← collectionOpIdent factory "Sequence.build" [et])
        (.arrow (seqTy et) (.arrow et (seqTy et))) ctx pending
    litElemsToSMTTerm factory et (bld [acc, xT] bty) rest ctx pending
end

mutual

@[expose]
def toSMTTerm (factory : @Lambda.Factory CoreLParams) (bvs : BoundVars) (e : LExpr CoreLParams.mono) (ctx : SMT.Context)
  (pending : SMT.PendingFnQueue)
  : Except Format (Term × SMT.Context × SMT.PendingFnQueue) := do
  match e with
  | .const _ c =>
    -- An ill-typed literal has type `bool` (`LConst.ty`), so its encoding would disagree
    -- with its type.
    if c.wt then litToSMTTerm factory c ctx pending
    else .error f!"Cannot encode the ill-typed literal {e}."
  | .op _ fn fnty =>
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}."
    | some fnty =>
      let (op, retty, ctx, pending) ← toSMTOp factory fn fnty ctx pending
      match LMonoTy.splitArrows (ctx.opArity factory fn fnty) fnty with
      | ([], _) => .ok (op [] retty, ctx, pending)
      | (intys, _) =>
        -- The value's array sort would be indexed by an array: refuse it here rather
        -- than emit a sort the solver rejects.
        if hasArrayIndexedByArray ctx.useArrayTheory fnty then
          throw (arrayIndexedByArrayError fnty (!hasArrayIndexedByArray false fnty))
        let (t, ctx) ← functionValueToSMT fn intys op retty ctx
        .ok (t, ctx, pending)

  | .bvar _ i =>
    if h: i < bvs.length
    then do
      let var := bvs[i]
      .ok ((TermVar.mk var.fst var.snd), ctx, pending)
    else .error f!"Bound variable index is out of bounds: {i}"

  | .fvar _ f ty =>
    match ty with
    | none => .error f!"Cannot encode unannotated free variable {e}"
    | some ty =>
      let (uf, ctx) ← fvarToUF f ty ctx
      if !uf.args.isEmpty then
        -- A variable whose array sort would be indexed by an array is applied as an
        -- uninterpreted function; used as a value, it is a constant of an opaque sort,
        -- unrelated to its applications. Every model of the program extends to one of
        -- the query, as when every function type was an opaque sort: comparing two such
        -- values gets a verdict, and an `unsat` answer stays sound.
        let sortName := "$__FunctionValue"
        let ctx := ctx.addSort { name := sortName, arity := 0 }
        let srt : TermType := .constr sortName []
        let cst : UF := { id := s!"{uf.id}$value", args := [], out := srt }
        return (.app (.uf cst) [] srt, ctx.addUF cst, pending)
      .ok (.app (.uf uf) [] uf.out, ctx.addUF uf, pending)

  | .abs _ _ _ _ =>
    .error f!"Cannot encode lambda expression to SMT. \
              Lambda abstractions must be eliminated (by the `lambdaLift` phase) \
              before SMT encoding.\n\
              Lambda: {e}"

  | .quant _ _ _ .none _ _ => .error f!"Cannot encode untyped quantifier {e}"
  | .quant _ qk name (.some ty) tr e =>
    let fvarNames := (e.collectFvarNames.map (·.name)).toArray
    -- Prefer the user-provided binder name; when absent, fall back to a
    -- depth-based `$__bv{N}` name (`N` = the binder's de Bruijn depth, i.e. the
    -- current binder-stack size). The `$__` prefix is reserved for internal use
    -- and cannot appear in user identifiers. `findUnique` (below) then resolves
    -- any residual clash against the names in scope, so the base need only be
    -- unique along a root-to-leaf binder path — which depth guarantees.
    let (baseName, startSuffix) :=
      if name.isEmpty then
        (s!"$__bv{bvs.length}", 1)
      else
        Strata.Name.breakDisambiguated name
    -- Check for clashes with existing bvars, fvars, sorts, datatypes, and fvars in body
    let usedNames := Std.HashSet.ofList (bvs.map (·.1) ++ ctx.ufs.toList.map (·.id) ++ fvarNames.toList
      ++ ctx.sorts.toList.map (·.name) ++ ctx.seenDatatypes.toList)
    let x := Strata.Name.findUnique baseName startSuffix usedNames
    let (ety, ctx) ← LMonoTy.toSMTType ty ctx
    -- Lower the Core trigger expression into `List (List Term)` pattern groups; leaf
    -- pattern terms are encoded with the binder `x` in scope.
    let trBvs := (x, ety) :: bvs
    let (trGroups, ctx, pending) ←
      if isCoreTriggerListExpr tr then
        encodeTriggerGroups factory trBvs tr [] ctx pending
      else
        -- A single pattern term forms one `:pattern` group.
        let (tt, ctx, pending) ← toSMTTerm factory trBvs tr ctx pending
        .ok ([[tt]], ctx, pending)
    let (et, ctx, pending) ← toSMTTerm factory trBvs e ctx pending
    .ok (Factory.quant (convertQuantifierKind qk) x ety trGroups et, ctx, pending)
  | .eq _ e1 e2 =>
    let (e1t, ctx, pending) ← toSMTTerm factory bvs e1 ctx pending
    let (e2t, ctx, pending) ← toSMTTerm factory bvs e2 ctx pending
    .ok ((Factory.eq e1t e2t), ctx, pending)

  | .ite _ c t f =>
    let (ct, ctx, pending) ← toSMTTerm factory bvs c ctx pending
    let (tt, ctx, pending) ← toSMTTerm factory bvs t ctx pending
    let (ft, ctx, pending) ← toSMTTerm factory bvs f ctx pending
    .ok ((Factory.ite ct tt ft), ctx, pending)

  | .app _ fn arg =>
    appToSMTTerm factory bvs fn arg [] ctx pending
termination_by (sizeOf e, 1)
decreasing_by
  all_goals simp_wf
  all_goals (first | omega | term_by_mem)

/-- Encode an application `fn arg` (with already-encoded trailing arguments
    `acc`) to an SMT term.

    `fn`/`arg` are the two children of an `LExpr.app` node; splitting them out
    in the signature (rather than taking the whole `.app`) makes it a type-level
    invariant that this function is only ever called on applications, so there
    is no "not an application" fallthrough to handle. The head of the spine is
    reached by recursing on `fn`; `acc` accumulates the encoded arguments from
    right to left as the spine is peeled. -/
def appToSMTTerm (factory : @Lambda.Factory CoreLParams) (bvs : BoundVars) (fn arg : LExpr CoreLParams.mono)
  (acc : List Term) (ctx : SMT.Context)
  (pending : SMT.PendingFnQueue) :
  Except Format (Term × SMT.Context × SMT.PendingFnQueue) := do
  match fn, arg with
  -- Special case for indexed SMT operations. The loop bounds must be natural
  -- number literals. Partial evaluation reduces the index expressions to
  -- `.intConst` before SMT encoding *when the surrounding function is inlined*;
  -- a `re.loop` inside a non-inlined function body (encoded as a UF) can still
  -- carry symbolic indices, so we keep the explicit error for that case.
  | .app _ (.app _ (.op _ "Re.Loop" _) x) n1, n2 =>
    let (xt, ctx, pending) ← toSMTTerm factory bvs x ctx pending
    match n1, n2 with
    | .intConst _ n1i, .intConst _ n2i =>
      match Int.toNat? n1i, Int.toNat? n2i with
      | .some n1n, .some n2n =>
        .ok (.app (Op.re_loop n1n n2n) [xt] .regex, ctx, pending)
      | _, _ => .error f!"Natural numbers expected as indices for re.loop.\n\
                          Original expression: {(LExpr.app smtEncodingLoc fn arg).eraseTypes}"
    | _, _ => .error f!"Natural numbers expected as indices for re.loop.\n\
                        Original expression: {(LExpr.app smtEncodingLoc fn arg).eraseTypes}"

  | .app _ fn' e1, e2 => do
    let (e2t, ctx, pending) ← toSMTTerm factory bvs e2 ctx pending
    appToSMTTerm factory bvs fn' e1 (e2t :: acc) ctx pending

  | .op _ fn fnty, e1 => do
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}. \n\
                        Appears in expression: {LExpr.app smtEncodingLoc (LExpr.op smtEncodingLoc
                            fn fnty) e1}"
    | some fnty =>
      let (op, retty, ctx, pending) ← toSMTOp factory fn fnty ctx pending
      let (e1t, ctx, pending) ← toSMTTerm factory bvs e1 ctx pending
      let args := e1t :: acc
      let arity := ctx.opArity factory fn fnty
      if args.length < arity then
        .error f!"Cannot encode partial application of {fn} to SMT: \
                  it takes {arity} arguments but is applied to {args.length}. \n\
                  Appears in expression: \
                  {LExpr.app smtEncodingLoc (LExpr.op smtEncodingLoc fn fnty) e1}"
      else
        let (direct, extra) := args.splitAt arity
        .ok (selectAll (op direct retty) extra, ctx, pending)
  | .fvar _ fn (.some fnty), e1 => do
    let (uf, ctx) ← fvarToUF fn fnty ctx
    let (e1t, ctx, pending) ← toSMTTerm factory bvs e1 ctx pending
    let allArgs := e1t :: acc
    if allArgs.length < uf.args.length then
      -- Its function value is opaque (`fvarToUF`), so a partial application has no array to
      -- select from.
      throw f!"Cannot encode partial application of {fn} to SMT: its type '{fnty}' would be \
               an array indexed by an array, so it is encoded as an uninterpreted function \
               of its {uf.args.length} arguments, but is applied to {allArgs.length}."
    let (direct, extra) := allArgs.splitAt uf.args.length
    .ok (selectAll (Term.app (.uf uf) direct uf.out) extra, ctx.addUF uf, pending)
  -- A bound variable or a conditional of function type is a function value (an SMT
  -- array): apply it by `select`.
  | .bvar _ i, a => do
    let fnt ← if h : i < bvs.length then
        let var := bvs[i]
        pure (Term.var (TermVar.mk var.fst var.snd))
      else .error f!"Bound variable index is out of bounds: {i}"
    let (argt, ctx, pending) ← toSMTTerm factory bvs a ctx pending
    .ok (selectAll fnt (argt :: acc), ctx, pending)
  | .ite _ c t f, a => do
    let (ct, ctx, pending) ← toSMTTerm factory bvs c ctx pending
    if hasOpaqueFunctionValue ctx.useArrayTheory t ||
        hasOpaqueFunctionValue ctx.useArrayTheory f then
      -- A branch is a variable whose function value is an opaque constant, which can only
      -- be applied as its uninterpreted function: the application is pushed into the
      -- branches, `(if c then t else f)(a)` being `if c then t(a) else f(a)`.
      let (tt, ctx, pending) ← appToSMTTerm factory bvs t a acc ctx pending
      let (ft, ctx, pending) ← appToSMTTerm factory bvs f a acc ctx pending
      .ok (Factory.ite ct tt ft, ctx, pending)
    else
      -- Both branches are arrays: the conditional is one, applied once by `select`, with
      -- the argument encoded once.
      let (tt, ctx, pending) ← toSMTTerm factory bvs t ctx pending
      let (ft, ctx, pending) ← toSMTTerm factory bvs f ctx pending
      let (argt, ctx, pending) ← toSMTTerm factory bvs a ctx pending
      .ok (selectAll (Factory.ite ct tt ft) (argt :: acc), ctx, pending)
  | _, _ =>
    .error f!"Cannot encode .app expression {LExpr.app smtEncodingLoc fn arg}"
termination_by (sizeOf fn + sizeOf arg, 0)
decreasing_by
  all_goals simp_wf
  all_goals (first | omega | term_by_mem)

/-- Decompose one Core trigger *group* — a `TriggerGroup.addTrigger` spine ending
    in `TriggerGroup.empty` (as produced by `Core.Factory.mkTriggerGroup`) — into
    the list of encoded SMT pattern terms it holds, in source order. -/
def encodeTriggerGroup (factory : @Lambda.Factory CoreLParams) (bvs : BoundVars)
  (g : LExpr CoreLParams.mono) (acc : List Term) (ctx : SMT.Context)
  (pending : SMT.PendingFnQueue)
  : Except Format (List Term × SMT.Context × SMT.PendingFnQueue) := do
  match g with
  | .op _ _ _ =>
    -- `TriggerGroup.empty`: end of the group spine.
    .ok (acc, ctx, pending)
  | .app _ (.app _ (.op _ opId _) t) rest =>
    match CoreOp.ofString opId.name with
    | .trigger .AddTrigger =>
      let (tt, ctx, pending) ← toSMTTerm factory bvs t ctx pending
      encodeTriggerGroup factory bvs rest (tt :: acc) ctx pending
    | _ => .error f!"Unexpected operator in trigger group: {opId.name}"
  | _ => .error f!"Unexpected trigger group expression: {g}"
termination_by (sizeOf g, 0)
decreasing_by
  all_goals simp_wf
  all_goals (first | omega | term_by_mem)

/-- Decompose a structured Core trigger LExpr — a `Triggers.addGroup` spine ending
    in `Triggers.empty` (as produced by `Core.Factory.mkTriggerExpr`), or
    `LExpr.noTrigger` (a bare `.bvar`) when absent — into SMT `:pattern` groups, in
    source order. Direct (unstructured) pattern-term triggers are handled by the
    caller, not here. -/
def encodeTriggerGroups (factory : @Lambda.Factory CoreLParams) (bvs : BoundVars)
  (tr : LExpr CoreLParams.mono) (acc : List (List Term)) (ctx : SMT.Context)
  (pending : SMT.PendingFnQueue)
  : Except Format (List (List Term) × SMT.Context × SMT.PendingFnQueue) := do
  match tr with
  | .bvar _ _ =>
    -- `LExpr.noTrigger`: no meaningful trigger.
    .ok (acc, ctx, pending)
  | .op _ _ _ =>
    -- `Triggers.empty`: end of the group-list spine.
    .ok (acc, ctx, pending)
  | .app _ (.app _ (.op _ opId _) g) rest =>
    match CoreOp.ofString opId.name with
    | .trigger .AddGroup =>
      let (group, ctx, pending) ← encodeTriggerGroup factory bvs g [] ctx pending
      encodeTriggerGroups factory bvs rest (group :: acc) ctx pending
    | _ => .error f!"Unexpected operator in trigger list: {opId.name}"
  | _ => .error f!"Unexpected trigger expression: {tr}"
termination_by (sizeOf tr, 0)
decreasing_by
  all_goals simp_wf
  all_goals (first | omega | term_by_mem)

end

/--
Encode a single deferred function `p`: encode its interpreted body (if any) and
its axioms to SMT `Term`s, returning the resolved
definition together with the (further) functions those terms reference.
`seen` holds the functions whose resolution is in progress or done.
-/
def resolveOnePendingFnDef (factory : @Lambda.Factory CoreLParams)
    (ctx : SMT.Context) (seen : Std.HashSet UF) (p : SMT.PendingFnDef) :
    Except Format (SMT.EncodedFnDef × SMT.Context × List SMT.PendingFnDef) :=
  open LTy.Syntax in do
  ctx.checkMonomorphic
  let some func := factory[p.fn.name]?
    | .error f!"Cannot find function {p.fn} in Strata Core's Factory!"

  let (intys, _) := LMonoTy.splitArrows func.inputs.length p.fnty
  let formals := func.inputs.keys
  let formalStrs := formals.map (toString ∘ format)

  -- Encode arg types (needed for both interpreted and uninterpreted paths).
  let (smt_intys, ctx) ← LMonoTys.toSMTType intys ctx
  let args := formalStrs.zip smt_intys |>.map fun (n, ty) => ({ id := n, ty } : TermVar)
  -- Encode the body (interpreted functions) or leave it uninterpreted.  A
  -- recursive function stays uninterpreted (its per-constructor axioms carry
  -- the definition) unless `recFnsAsDefineFunRec` is on, in which case its
  -- body is encoded like any other and emitted as `define-fun-rec`.
  let recAsDef := func.isRecursive && ctx.recFnsAsDefineFunRec && func.body.isSome
  let (body?, ctx, pending) ←
    if func.isRecursive && !recAsDef then
      .ok (none, ctx, ({} : SMT.PendingFnQueue))
    else match func.body with
    | none => .ok (none, ctx, ({} : SMT.PendingFnQueue))
    | some body =>
      -- Substitute the formals in the function body with appropriate `.bvar`s.
      -- Use substFvarsLifting to properly lift indices under binders.
      let bvs := args.map fun v => (v.id, v.ty)
      let bvars := (List.range formals.length).map (fun i => LExpr.bvar smtEncodingLoc i)
      let body := LExpr.substFvarsLifting body (formals.zip bvars)
      let (term, ctx, pending) ← toSMTTerm factory bvs body ctx {}
      .ok (some term, ctx, pending)

  -- A `define-fun-rec` may refer to itself and to functions emitted before it;
  -- a recursive callee that is not yet committed is resolved and committed
  -- before `p`. A recursive callee whose resolution is still in progress
  -- calls back into `p` (mutual recursion), which would need
  -- `define-funs-rec`. That is not supported yet: fail rather than emit an
  -- ill-formed query.
  if recAsDef then
    if let some d := pending.toList.find? (fun d =>
        d.uf != p.uf && seen.contains d.uf && !ctx.committedFn d.uf
        && (factory[d.fn.name]?.map (·.isRecursive)).getD false) then
      throw f!"recursiveFnsAsDefineFunRec: '{p.fn}' and '{d.fn}' are mutually \
               recursive; define-funs-rec is not supported yet."
  -- Encode the function's axioms (recursive-function axioms are pre-computed by
  -- `Core.generateRecursiveAxioms` and carried in `func.axioms`).  All types
  -- are monomorphic post-`MonomorphizeFunctions`, so no type-variable
  -- substitution is needed to encode them.
  let (axiomTermsRev, ctx, pending) ← func.axioms.foldlM
    (init := (([] : List Term), ctx, pending))
    (fun (axs, ctx, pending) (ax : LExpr CoreLParams.mono) => do
      let (axiom_term, ctx, pending) ← toSMTTerm factory [] ax ctx pending
      .ok (axiom_term :: axs, ctx, pending))
  .ok ({ id := p.uf.id, args, out := p.uf.out, body?, axioms := axiomTermsRev.reverse,
         isRec := recAsDef },
       ctx, pending.toList)

/--
Resolve and commit the transitive closure of deferred function definitions
to `SMT.Context`.
The fuel is set to factory.toArray.size + pending.length, which is enough to
visit all bodies and axioms. It is used to make the termination proof easier.
-/
def processPendingFnDefsAux (factory : @Lambda.Factory CoreLParams) (fuel : Nat)
    (ctx : SMT.Context) (seen : Std.HashSet UF)
    (pending : List SMT.PendingFnDef) :
    Except Format SMT.Context := do
  match pending with
  | [] => .ok ctx
  | p :: rest =>
    -- Skip functions already committed to `ctx` or already in progress.
    if ctx.committedFn p.uf || seen.contains p.uf then
      processPendingFnDefsAux factory fuel ctx seen rest
    else
      match fuel with
      | 0 => .error f!"Ran out of fuel resolving SMT function definitions \
                       (cycle or factory larger than expected) at '{p.fn}'."
      | fuel + 1 =>
        -- Mark `p` in progress *before* encoding so a self/mutual reference in
        -- its body or axioms does not re-schedule it.
        let seen := seen.insert p.uf
        let (rdef, ctx, deps) ← resolveOnePendingFnDef factory ctx seen p
        -- Commit the dependencies discovered while encoding `p` first, so they
        -- are committed before `p` (callee-before-caller), then commit `p`.
        let ctx ← processPendingFnDefsAux factory fuel ctx seen deps
        let ctx := ctx.addResolvedFnDef rdef
        processPendingFnDefsAux factory fuel ctx seen rest
termination_by (fuel, pending.length)
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Resolve and commit all deferred function definitions in `pending` to `ctx`.
    The initial fuel covers the factory size (each function is committed at most
    once). -/
def processPendingFnDefs (factory : @Lambda.Factory CoreLParams)
    (ctx : SMT.Context) (pending : SMT.PendingFnQueue) : Except Format SMT.Context := do
  ctx.checkMonomorphic
  processPendingFnDefsAux factory (factory.toArray.size + pending.size) ctx {} pending.toList

def toSMTTerms (factory : @Lambda.Factory CoreLParams) (es : List (LExpr CoreLParams.mono)) (ctx : SMT.Context)
  (pending : SMT.PendingFnQueue) :
  Except Format ((List Term) × SMT.Context × SMT.PendingFnQueue) := do
  ctx.checkMonomorphic
  go es ctx pending #[]
where
  go (es : List (LExpr CoreLParams.mono)) (ctx : SMT.Context) (pending : SMT.PendingFnQueue)
     (acc : Array Term) :
     Except Format ((List Term) × SMT.Context × SMT.PendingFnQueue) := do
    match es with
    | [] => return (acc.toList, ctx, pending)
    | e :: erest =>
      let (et, ctx, pending) ← toSMTTerm factory [] e ctx pending
      go erest ctx pending (acc.push et)

/--
A variable definition to be emitted as `define-fun` in SMT-LIB.
Contains the variable name, its SMT type, and the encoded body term.
-/
structure VarDefinition where
  name : String
  ty : Strata.SMT.TermType
  body : Term

/--
A variable declaration to be emitted as `declare-fun` in SMT-LIB.
Contains the variable name and its SMT type.
-/
structure VarDeclaration where
  name : String
  ty : Strata.SMT.TermType

/-! ### Per-item encoding workers -/

/-- Encode one plain assumption entry. Lambda redexes in assumption/obligation
    terms (e.g. an argument-value precondition modelled as
    `(fun _ : string => true)(arg)`) are contracted by the `betaReduce`
    pipeline phase; a redex reaching `appToSMTTerm`'s catch-all here would
    fail with "Cannot encode .app expression". -/
def SMT.encodeAssumptionItem (factory : @Lambda.Factory CoreLParams)
    (e : LExpr CoreLParams.mono) (ctx : SMT.Context) (pending : SMT.PendingFnQueue) :
    Except Format (Term × SMT.Context × SMT.PendingFnQueue) :=
  Core.toSMTTerm factory [] e ctx pending

/-- Encode one distinctness group entry into a single `distinct` assertion. SMT-LIB's
    `distinct` takes two or more terms, so a group of fewer expressions, which holds
    trivially, is encoded as `true`. -/
def SMT.encodeDistinctItem (factory : @Lambda.Factory CoreLParams)
    (es : List (LExpr CoreLParams.mono)) (ctx : SMT.Context) (pending : SMT.PendingFnQueue) :
    Except Format (Term × SMT.Context × SMT.PendingFnQueue) := do
  let (ts, ctx, pending) ← Core.toSMTTerms factory es ctx pending
  match ts with
  | _ :: _ :: _ => .ok (Term.app (.core .distinct) ts .bool, ctx, pending)
  | _ => .ok (Term.bool true, ctx, pending)

/-- Encode one variable-definition entry (`init name ty (.det e)`), emitted by
    callers as `define-fun`. -/
def SMT.encodeVarDefItem (factory : @Lambda.Factory CoreLParams)
    (item : CoreIdent × Expression.Ty × LExpr CoreLParams.mono)
    (ctx : SMT.Context) (pending : SMT.PendingFnQueue) :
    Except Format (VarDefinition × SMT.Context × SMT.PendingFnQueue) := do
  let (name, ty, rhs) := item
  if h : ty.isMonoType then
    let (smtTy, ctx) ← LMonoTy.toSMTType (ty.toMonoType h) ctx
    let (rhsTerm, ctx, pending) ← Core.toSMTTerm factory [] rhs ctx pending
    .ok ({ name := name.name, ty := smtTy, body := rhsTerm }, ctx, pending)
  else
    .error f!"SMT encoding: variable definition '{name.name}' has non-monomorphic type"

/-- Encode one variable-declaration entry (`init name ty .nondet`), emitted by
    callers as `declare-fun`. Declarations have no body, so they schedule no
    deferred functions and need not thread the pending queue. -/
def SMT.encodeVarDeclItem (item : CoreIdent × Expression.Ty) (ctx : SMT.Context) :
    Except Format (VarDeclaration × SMT.Context) := do
  let (name, ty) := item
  if h : ty.isMonoType then
    let (smtTy, ctx) ← LMonoTy.toSMTType (ty.toMonoType h) ctx
    .ok ({ name := name.name, ty := smtTy }, ctx)
  else
    .error f!"SMT encoding: variable declaration '{name.name}' has non-monomorphic type"

---------------------------------------------------------------------

/-- Convert an expression of type LExpr to a String representation in SMT-Lib syntax, for testing.
    Outputs variable declarations followed by the assertion of the encoded term. -/
def toSMTCommandsWithAssert (e : LExpr CoreLParams.mono)
  (factory : @Lambda.Factory CoreLParams := Core.Factory) (ctx : SMT.Context := SMT.Context.default)
  : IO String := do
  let smtctx := toSMTTerm factory [] e ctx {}
  match smtctx with
  | .error e => return e.pretty
  | .ok (smt, _, _) =>
    let b ← IO.mkRef { : IO.FS.Stream.Buffer }
    let solver ← Solver.bufferWriter b
    let (encoded, _) ← (((Encoder.encodeTerm smt).run EncoderState.init).run).run solver
    match encoded with
    | .error err => return toString err
    | .ok (enc, _) =>
      let (asserted, _) ← ((Solver.assert enc).run).run solver
      match asserted with
      | .error err => return toString err
      | .ok () =>
        let contents ← b.get
        if h: contents.data.IsValidUTF8
        then return String.fromUTF8 contents.data h
        else return "Converting SMT Term to bytes produced an invalid UTF-8 sequence."

/-- Whether a term is a real literal (top-level only). -/
def smtTermIsReal : Strata.SMT.Term → Bool
  | .prim (.real _) => true
  | _               => false

/-- The rational a model term spells, if it is one: `(/ p q)` over numeric literals `p`
    and `q ≠ 0` (how a solver prints a non-integral real), or `(- r)` over such a
    rational. -/
def smtTermRational? : Strata.SMT.Term → Option Rat
  | .app (.core (.uf uf)) [p, q] _ =>
    if uf.id != "/" then none else do
      let q ← literal q
      if q == 0 then none else return (← literal p) / q
  | .app (.core (.uf uf)) [r] _ => if uf.id == "-" then (smtTermRational? r).map (- ·) else none
  | _ => none
where
  /-- The value of a numeric literal. -/
  literal : Strata.SMT.Term → Option Rat
    | .prim (.int i) => some i
    | .prim (.real d) => some d.toRat
    | _ => none

/--
Convert an `SMT.Term` back to a Core `LExpr` (best-effort, partial inverse of `toSMTTerm`).

Handles:
- Primitives: bool, int, real, bitvec, string
- Rationals `(/ p q)` (`smtTermRational?`), as real literals
- UF applications (free variables, constructors, uninterpreted functions)
- Datatype constructors/selectors/testers

Falls back to rendering the term as a free variable with its string representation
for any unsupported term shape.

`constructorNames` is the set of known datatype constructor names.  When a
bare `SMT.Term.var` matches a constructor name (zero-argument constructor
such as `Nil`), the result uses `.op` instead of `.fvar` so that the
counterexample formatter can distinguish constructors from plain variables
and render them with the correct Core data structure.
-/
def smtTermToLExpr (t : Strata.SMT.Term)
    (constructorNames : Std.HashSet String := {}) : LExpr CoreLParams.mono :=
  match t with
  | .prim (.bool b)       => .boolConst smtModelLoc b
  | .prim (.int i)        => .intConst smtModelLoc i
  | .prim (.real d)       => .rationalConst smtModelLoc d.toRat
  | .prim (.bitvec b)     => .bitvecConst smtModelLoc _ b
  | .prim (.string s)     => .strConst smtModelLoc s
  | .var v                =>
    -- Zero-arg constructors arrive as plain variables from the SMT solver.
    -- Mark them with `.op` so the formatter can emit `Name()`.
    if constructorNames.contains v.id then
      .op smtModelLoc v.id none
    else
      .fvar smtModelLoc (coreValueName v.id) none
  | .app (.core (.uf uf)) args _retTy =>
    match smtTermRational? t with
    | some r => .rationalConst smtModelLoc r
    | none =>
    -- Constructor names use `.op` so the formatter can distinguish them
    -- from plain variables (e.g., `Nil` constructor must not be .fvar).
    --
    -- The model parser folds `(- <literal>)` into a negative literal, so a
    -- unary `-` reaches here only over a non-literal argument. Core has no `-`
    -- production, so map it to `Int.Neg`/`Real.Neg` to keep models
    -- re-parseable; such a term is not a value (see `smtTermIsValue`).
    let fnExpr : LExpr CoreLParams.mono :=
      match uf.id, args with
      | "-", [arg] => .op smtModelLoc (if smtTermIsReal arg then "Real.Neg" else "Int.Neg") none
      | _, _ =>
        if constructorNames.contains uf.id then
          .op smtModelLoc uf.id none
        else
          -- An abstract value arrives as a zero-argument UF named after its sort.
          .fvar smtModelLoc (coreValueName uf.id) none
    args.foldl (fun acc arg => .app smtModelLoc acc (smtTermToLExpr arg constructorNames)) fnExpr
  | .app (.datatype_op _kind name) args _retTy =>
    let fnExpr : LExpr CoreLParams.mono := .op smtModelLoc name none
    args.foldl (fun acc arg => .app smtModelLoc acc (smtTermToLExpr arg constructorNames)) fnExpr
  | .app op args _ =>
    -- Generic fallback for other ops: render as op name applied to args
    let opName := op.mkName
    let fnExpr : LExpr CoreLParams.mono := .op smtModelLoc opName none
    args.foldl (fun acc arg => .app smtModelLoc acc (smtTermToLExpr arg constructorNames)) fnExpr
  | .none _ty             => .op smtModelLoc "none" none
  | .some inner           => .app smtModelLoc (.op smtModelLoc "some" none) (smtTermToLExpr inner
      constructorNames)
  | .quant _ _ _ _        =>
    -- Quantifiers in model values are unusual; fall back to string repr
    let s := match Strata.SMTDDM.termToString t with
             | .ok s => s | .error _ => repr t |>.pretty
    .fvar smtModelLoc s none

/--
Extract the set of datatype constructor names from an `SMT.Context`.
-/
def SMT.Context.getConstructorNames (ctx : SMT.Context) : Std.HashSet String :=
  ctx.datatypeFuns.fold (init := {}) fun acc name (kind, _) =>
    if kind == .constructor then acc.insert name else acc

/--
Decide whether an `SMT.Term` from a solver model is a *recognized value* — a
term whose lift to `LExpr` (via `smtTermToLExpr`) lands on an interpretable
value rather than one of that lift's lossy catch-alls.

`true` exactly when the term is either
- a primitive value (`.prim`: bool/int/real/bitvec/string), or
- a rational (`smtTermRational?`), or
- a datatype constructor application: `.app (.core (.uf {id})) args` with
  `id ∈ constructorNames` and every argument itself a value.

Everything else is `false`: a real (uninterpreted-function) value, an
uninterpreted-sort element, an array value, a `.some`/`.none` option wrapper, a
`.quant`, a `.var` (even a zero-arg constructor arrives as `.var`; the model
parser used here does not emit `.var`, so this is conservatively non-value), and
any UF application whose head is not a known constructor or whose arguments are
not all values.

This is the value discriminator the VC check uses to decide which model
bindings may enter the evaluation environment; it mirrors, term-for-term, where
`smtTermToLExpr` produces something the evaluator cannot soundly consume. -/
def smtTermIsValue (t : Strata.SMT.Term)
    (constructorNames : Std.HashSet String := {}) : Bool :=
  match t with
  | .prim _ => true
  | t@(.app (.core (.uf uf)) args _retTy) =>
    (smtTermRational? t).isSome || constructorNames.contains uf.id &&
      args.attach.all (fun ⟨a, _⟩ => smtTermIsValue a constructorNames)
  | _ => false
termination_by sizeOf t
decreasing_by all_goals (first | omega | term_by_mem)

/--
Convert a model map from `SMT.Term` values to `LExpr` values,
so that model values can be displayed using Core's expression formatter.

`constructorNames` allows zero-argument constructors (which the SMT solver
returns as plain variables) to be distinguished from ordinary variables (.fvar)
-/
def convertModel (model : Imperative.SMT.Model Expression.Ident)
    (constructorNames : Std.HashSet String := {})
    : List (Expression.Ident × LExpr CoreLParams.mono) :=
  model.map fun (id, t) => (id, smtTermToLExpr t constructorNames)

/-- Backward-compatible alias. -/
@[deprecated convertModel (since := "2026-04-03")] abbrev convertCounterEx := @convertModel

/-! ## Shared-prefix obligation encoder

Encodes an env's obligations in arrival order, encoding each
`PathConditionEntry` of their `assumptions` once, instead of re-encoding
every obligation's full `assumptions` from scratch.

The incremental machinery is the `Imperative.PathConditionsFold` fold; this
section instantiates it (`smtEncodingFold`): the checkpoint `σ` is an
`SMTCheckpoint` (the accumulated `SMT.Context`), the per-frame output `ω` is an
`SMTEncodedPathCondition` (each entry's encoded term or deferred error, plus the
factory-function definitions that term depends on), and the step is
`encodePathConditionEntry`. Per obligation, `encodeObligationToSMT` encodes
whichever of the obligation's `assumptions` the state has not already encoded,
then *snapshots* the obligation: it reads the obligation's complete
`EncodeResult` out of the shared state without writing anything back, so the
goal never enters the shared state.

The state holds the full, unpruned `assumptions`, so entries stay shared
across obligations that prune different irrelevant axioms or leave out
different unread definitions. An entry's term, any encoding error, and its
definition dependencies are attributed to that entry, so `snapshotObligation`
selects only the entries an obligation keeps, an assumption or distinctness
fact by its label (`prunedLabels`) and a variable definition by its variable's
name (`unreadDefs`), two separate sets: a pruned
entry's term is never asserted or defined, its error is never surfaced, and its
definitions are never drained — for these three mechanisms the result matches
a from-scratch encoding of the pruned obligation.

Declarations are the exception: encoding an entry registers the sorts and
free-variable UFs it mentions in the shared `SMT.Context` by side effect
(first mention wins), with no per-entry attribution. A pruned entry's
registrations therefore remain in the context and are emitted as `declare-sort`
/ `declare-fun` lines a pruned-first encoding would not contain. These are
semantically inert (solvers treat unused declarations as no-ops; verification
results are unaffected).

See `SMTEncoderProps.lean` for `encodeRun_eq_reference`: threading one
state across an env's obligations produces exactly the results of encoding
each obligation independently from scratch. -/

/-- The encoder's checkpoint: the accumulated `SMT.Context`. -/
structure SMTCheckpoint where
  ctx : SMT.Context

/-- One entry's complete, self-contained encoding contribution: either the
    encoded term together with the factory-function definitions it depends on
    (its own fresh `PendingFnQueue`), or the encoding error.

    Deferring the error into the output — rather than failing the fold — lets
    `snapshotObligation` surface it only for obligations that keep the entry's
    label; capturing the per-entry queue lets the drain be seeded from kept
    entries alone. -/
structure EncodedEntry where
  label : String
  result : Except Format (Term × SMT.PendingFnQueue)

/-- The encoded contributions of one frame, one list per `PathConditionEntry`
    kind, each reversed for O(1) accumulation.

    Assumptions and distincts are label-prunable, so each is stored as an
    `EncodedEntry` whose error is deferred. Variable definitions/declarations
    are program variables, so they are stored eagerly; a `varDef` additionally
    carries its definition dependencies. -/
structure SMTEncodedPathCondition where
  assumptionsRev : List EncodedEntry := []
  distinctsRev : List EncodedEntry := []
  varDefsRev : List (VarDefinition × SMT.PendingFnQueue) := []
  varDeclsRev : List VarDeclaration := []

/-- Encode one `PathConditionEntry` against the accumulated context
    (`current.ctx`), returning the updated `SMTCheckpoint` and `out` extended
    with the entry's contribution. Serves as the step function of the
    incremental fold.

    Each entry is encoded against a *fresh* PendingFnQueue, so the returned queue
    is exactly this entry's direct factory-function references.
    Assumption/distinct encoding errors are deferred into the output and leave
    the checkpoint unchanged; they become fatal only if a snapshot keeps
    the entry's label. -/
def encodePathConditionEntry (factory : @Lambda.Factory CoreLParams) (current : SMTCheckpoint)
    (out : SMTEncodedPathCondition) (e : PathConditionEntry Expression) :
    Except Format (SMTCheckpoint × SMTEncodedPathCondition) := do
  match e with
  | .assumption label expr =>
    match SMT.encodeAssumptionItem factory expr current.ctx {} with
    | .ok (t, ctx, pending) =>
      let entry : EncodedEntry := { label, result := .ok (t, pending) }
      .ok ({ ctx }, { out with assumptionsRev := entry :: out.assumptionsRev })
    | .error err =>
      let entry : EncodedEntry := { label, result := .error err }
      .ok (current, { out with assumptionsRev := entry :: out.assumptionsRev })
  | .distinct label exprs =>
    match SMT.encodeDistinctItem factory exprs current.ctx {} with
    | .ok (t, ctx, pending) =>
      let entry : EncodedEntry := { label, result := .ok (t, pending) }
      .ok ({ ctx }, { out with distinctsRev := entry :: out.distinctsRev })
    | .error err =>
      let entry : EncodedEntry := { label, result := .error err }
      .ok (current, { out with distinctsRev := entry :: out.distinctsRev })
  | .varDecl name ty (.det rhs) =>
    let (d, ctx, pending) ← SMT.encodeVarDefItem factory (name, ty, rhs) current.ctx {}
    .ok ({ ctx }, { out with varDefsRev := (d, pending) :: out.varDefsRev })
  | .varDecl name ty .nondet =>
    let (d, ctx) ← SMT.encodeVarDeclItem (name, ty) current.ctx
    .ok ({ ctx }, { out with varDeclsRev := d :: out.varDeclsRev })

/-- The SMT instantiation of the `PathConditionsFold` backend: each
    `PathConditionEntry` is encoded to an SMT term against an `SMTCheckpoint`,
    accumulating per-frame `SMTEncodedPathCondition`s. -/
def smtEncodingFold (factory : @Lambda.Factory CoreLParams) :
    Fold Format SMTCheckpoint SMTEncodedPathCondition Expression where
  stepEntry := encodePathConditionEntry factory
  emptyOutput := {}

/-- The SMT encoder's fold state: the generic
    `Imperative.PathConditions.FoldState` instantiated at the SMT backend's
    checkpoint and output types. -/
abbrev SMTEncodeState := FoldState SMTCheckpoint SMTEncodedPathCondition Expression

/-! ## Per-obligation snapshots

The fold state holds entry encodings shared by many obligations. A *snapshot*
builds one obligation's SMT query from it. The state is left untouched for
the next obligation.

Snapshots are built in two stages. `EncodeResult.Assembly` is the
goal-independent part: the kept entries' terms and drain seed. It depends
only on the fold state's `frames`, so it is memoizable. `Assembly.finish`
then folds in the obligation's goal and drains its definition dependencies. -/

/-- One obligation's encoded SMT query. -/
structure EncodeResult where
  /-- Terms to assert: kept distincts, then kept assumptions. -/
  assumptions : List Term
  /-- Variable definitions (emitted as `define-fun`). -/
  varDefs : List VarDefinition
  /-- Variable declarations (emitted as `declare-fun`). -/
  varDecls : List VarDeclaration
  /-- The encoded goal term. -/
  goal : Term
  /-- The context after draining the definitions the terms depend on. -/
  ctx : SMT.Context
  /-- Encoding statistics for this obligation. -/
  stats : Statistics

/-- The context `r`'s query is declared from. With `removeDatatypes`, it
    declares only the datatypes that the query's text mentions and the
    datatypes their constructor fields use. The text is the kept assumptions,
    the goal, the variable declarations and definitions, and the functions
    and axioms of the context, which every emitter declares in full.
    Emission relies on the kept set containing every datatype the emitted
    query mentions and every field type of each kept datatype, and on every
    datatype being declared when `reachable` gives up. -/
-- TODO: prove this closure property.
def EncodeResult.declaredCtx (r : EncodeResult) (removeDatatypes : Bool) :
    SMT.Context := Id.run do
  if !removeDatatypes then return r.ctx
  let ctx := r.ctx
  let mut used := r.assumptions.foldl (fun acc t => t.addSortNames acc)
    (r.goal.addSortNames {})
  for d in r.varDefs do
    used := d.body.addSortNames (d.ty.addSortNames used)
  for d in r.varDecls do
    used := d.ty.addSortNames used
  for uf in ctx.ufs.toArray do
    used := uf.out.addSortNames (uf.args.foldl TermType.addSortNames used)
  for f in ctx.ifs.toArray do
    used := f.args.foldl TermVar.addSortNames used
    used := f.body.addSortNames (f.out.addSortNames used)
  for ax in ctx.axms.toArray do
    used := ax.addSortNames used
  let seen := ctx.seenDatatypes
  let fieldTypes := fun d => match ctx.datatypes.getType d with
    | some dt => dt.fieldTypeRefs.filter seen.contains
    | none => []
  -- `used` holds SMT-LIB sort names; `seen` holds Core datatype names.
  match Strata.Worklist.reachable (seen.toList.filter (used.contains <| smtSortName ·))
      fieldTypes seen.size with
  | some kept => return { ctx with seenDatatypes := kept }
  | none => return ctx

/-- The goal-independent stage of an `EncodeResult`: the kept entries' terms
    and drain seed, assembled from the frame list. -/
structure EncodeResult.Assembly where
  distincts : List Term
  assumptions : List Term
  varDefs : List VarDefinition
  varDecls : List VarDeclaration
  /-- Seed queue from the kept entries and varDefs (goal's queue not yet folded in). -/
  keptSeed : SMT.PendingFnQueue

/-- Assemble the entries kept: an assumption or distinctness fact when
    `keepLabel` holds of its label, a variable definition when `keepDef` holds of
    its variable's name. Their deferred results are forced (a kept entry's
    encoding error surfaces here; a dropped entry's never does). Emission order:
    newest frame first, in-frame program order. -/
def EncodeResult.Assembly.ofFramesKept (keepLabel keepDef : String → Bool)
    (frames : List (Imperative.PathConditions.PathConditionFrame
      SMTCheckpoint SMTEncodedPathCondition Expression)) :
    Except Format EncodeResult.Assembly := do
  let keptDistincts ← (frames.flatMap fun f =>
    f.output.distinctsRev.reverse.filterMap fun e =>
      if keepLabel e.label then some e.result else none).mapM id
  let keptAssumptions ← (frames.flatMap fun f =>
    f.output.assumptionsRev.reverse.filterMap fun e =>
      if keepLabel e.label then some e.result else none).mapM id
  let varDefsWithPending := frames.flatMap fun f =>
    f.output.varDefsRev.reverse.filter fun d => keepDef d.1.name
  -- Seed the drain from only the definitions the kept terms depend on;
  -- `processPendingFnDefs` rediscovers the transitive closure.
  let seedQueues : List SMT.PendingFnQueue :=
    keptAssumptions.map (·.2) ++ keptDistincts.map (·.2)
      ++ varDefsWithPending.map (·.2)
  let keptSeed : SMT.PendingFnQueue :=
    seedQueues.foldl (fun acc q => q.toList.foldl (·.insert ·) acc) ({} : SMT.PendingFnQueue)
  .ok { distincts := keptDistincts.map (·.1),
        assumptions := keptAssumptions.map (·.1),
        varDefs := varDefsWithPending.map (·.1),
        varDecls := frames.flatMap fun f => f.output.varDeclsRev.reverse,
        keptSeed }

/-- Complete an assembly into an `EncodeResult`: fold the goal's definition
    dependencies onto the seed, drain, and package. `ctx` is the context the
    goal was encoded against. -/
def EncodeResult.Assembly.finish (factory : @Lambda.Factory CoreLParams)
    (asm : EncodeResult.Assembly) (goalTerm : Term) (goalPending : SMT.PendingFnQueue)
    (ctx : SMT.Context) : Except Format EncodeResult := do
  let seed := goalPending.toList.foldl (·.insert ·) asm.keptSeed
  let ctx ← processPendingFnDefs factory ctx seed
  let stats : Statistics := ({} : Statistics)
    |>.increment s!"{Evaluator.Stats.smtProofObligation_numAssumptions}"
        (asm.distincts.length + asm.assumptions.length)
  .ok { assumptions := asm.distincts ++ asm.assumptions,
        varDefs := asm.varDefs, varDecls := asm.varDecls,
        goal := goalTerm, ctx, stats }

/-- Build one obligation's `EncodeResult` from `st` without writing back:
    encode the goal against `st.current`, assemble the entries kept (those whose
    label is not in `prunedLabels`, the definitions whose variable is not in
    `unreadDefs`), finish. -/
def snapshotObligation (factory : @Lambda.Factory CoreLParams) (st : SMTEncodeState)
    (goal : Expression.Expr) (prunedLabels : List String) (unreadDefs : Std.HashSet String) :
    Except Format EncodeResult := do
  -- Obligation-specific fork: encode the goal against a fresh queue, capturing
  -- the goal's own definition dependencies.
  let (goalTerm, ctx, goalPending) ←
    Core.toSMTTerm factory [] goal st.current.ctx {}
  -- Emission-time pruning: O(1) membership.
  let pruned : Std.HashSet String :=
    prunedLabels.foldl (fun acc l => acc.insert l) ∅
  let asm ← EncodeResult.Assembly.ofFramesKept (fun l => !pruned.contains l)
    (fun x => !unreadDefs.contains x) st.frames
  asm.finish factory goalTerm goalPending ctx

/-- Advance the fold over the obligation's `assumptions` (encoding only what
    the state has not already encoded), then `snapshotObligation` for its goal.
    Returns the result and the advanced state. -/
def encodeObligationToSMT (factory : @Lambda.Factory CoreLParams) (st : SMTEncodeState)
    (ob : Imperative.ProofObligation Expression) (prunedLabels : List String := [])
    (unreadDefs : Std.HashSet String := {}) :
    Except Format (EncodeResult × SMTEncodeState) := do
  -- `assumptions` lists its PathConditions newest first; the fold runs oldest first.
  let st ← ((smtEncodingFold factory).advance ob.assumptions.reverse).exec st
  let r ← snapshotObligation factory st ob.obligation prunedLabels unreadDefs
  .ok (r, st)

/-! ## Pointer-memoized snapshot assembly

Unpruned, the assembly depends only on the frame list, and adjacent
obligations usually share the identical list — so a single-slot
`Strata.PtrCache.PtrCache1` captures the reuse and a miss merely recomputes.
Pruning keeps a different entry subset per obligation, so pruned obligations
reassemble each time. -/

/-- Flatten the frames' per-kind outputs into one obligation's `Assembly`,
    keeping every entry. A named def so `PtrCache1` can memoize it. -/
def EncodeResult.Assembly.ofFrames
    (frames : List (Imperative.PathConditions.PathConditionFrame
      SMTCheckpoint SMTEncodedPathCondition Expression)) :
    Except Format EncodeResult.Assembly :=
  EncodeResult.Assembly.ofFramesKept (fun _ => true) (fun _ => true) frames

/-- `encodeObligationToSMT` with the assembly memoized by the frame list's
    pointer address. Pruned or sliced obligations delegate to `encodeObligationToSMT`,
    which is also available for callers without a cache to thread. -/
def encodeObligationToSMTCached (factory : @Lambda.Factory CoreLParams) (st : SMTEncodeState)
    (ob : Imperative.ProofObligation Expression) (prunedLabels : List String)
    (unreadDefs : Std.HashSet String)
    (cache : Strata.PtrCache.PtrCache1 EncodeResult.Assembly.ofFrames) :
    Except Format (EncodeResult × SMTEncodeState ×
      Strata.PtrCache.PtrCache1 EncodeResult.Assembly.ofFrames) := do
  if prunedLabels.isEmpty && unreadDefs.isEmpty then
    let st ← ((smtEncodingFold factory).advance ob.assumptions.reverse).exec st
    -- Encode the goal before assembling the entries: if both fail, the
    -- goal's error is reported.
    let (goalTerm, ctx, goalPending) ← Core.toSMTTerm factory [] ob.obligation st.current.ctx {}
    -- Miss continuation as an explicit lambda so the assembly runs only on a
    -- miss.
    let k : Strata.PtrCache.PtrCache1M EncodeResult.Assembly.ofFrames st.frames :=
      fun c => (⟨EncodeResult.Assembly.ofFrames st.frames, rfl⟩, c)
    let (res, cache) := (Strata.PtrCache.evalPtrCache1 st.frames k).run cache
    let asm ← res.output
    let r ← asm.finish factory goalTerm goalPending ctx
    .ok (r, st, cache)
  else
    let (r, st) ← encodeObligationToSMT factory st ob prunedLabels unreadDefs
    .ok (r, st, cache)

end -- public section

end Core
