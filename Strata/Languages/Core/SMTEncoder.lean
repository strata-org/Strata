/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.SMTUtils
public import Strata.DL.SMT.Factory
public import Strata.Languages.Core.Env
public import Strata.Util.Name
public import Strata.Util.OrderedSet
public import Strata.Util.Statistics
public import Strata.DL.SMT.DDMTransform.Translate -- shake: keep
import Strata.Languages.Core.Statistics
import Strata.Util.Tactics

---------------------------------------------------------------------

namespace Core
open Std (ToFormat Format format)
open Lambda Strata.SMT Strata.SMT.Encoder
open Strata.Util (OrderedSet)

public section
/--
A factory function whose UF declaration has been emitted but whose
definition (interpreted body and/or axioms) has not been encoded as SMT.Term yet.

`fn`/`fnty` are the call-site identifier and function type.
If fn was a polymorphic function, fnty is monomorphised at the call site.

`tySubst` is a snapshot of the encoder's type-variable substitution that was
active at the point of reference.
This is necessary for encoding the axioms of the function. A function discovered
while encoding a *polymorphic* referrer (e.g. `select` referenced inside
`update`'s axiom) has a `fnty` mentioning the referrer's type variables.
The snapshot lets the deferred resolution encode those types even though the
referrer's substitution is no longer otherwise in scope. -/
structure SMT.PendingFnDef where
  fn : CoreIdent
  uf : UF
  fnty : LMonoTy
  tySubst : Map String TermType
deriving Repr, Inhabited

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
deriving Repr, Inhabited

/--
SMT.Context holds the list of created SMT sorts, declared/defined functions, axioms,
type substitutions and others while translating Imperative.ProofObligation Expression to
SMT. This is one of the returned objects from ProofObligation.toSMTTerms.

SMT.Context also has fields that are invariant during translation; they are
explicitly marked as invariant in their comments.
-/
structure SMT.Context where
  /-- Declared SMT sorts, plus uninterpreted functions, defined functions, and
  axioms. Each is an `OrderedSet`, which keeps insertion order for emit while
  deduplicating in O(1) via a built-in membership index (the array and index
  cannot drift apart). -/
  sorts : OrderedSet Strata.DL.SMT.Sort := .empty
  ufs : OrderedSet UF := .empty
  ifs : OrderedSet IF := .empty
  axms : OrderedSet Term := .empty
  tySubst: Map String TermType := []
  /-- Stores the TypeFactory purely for ordering datatype declarations
  correctly (TypeFactory in topological order).
  It is seeded by the caller (from the env's datatype factory) before encoding
  and is not modified afterwards — it holds *all* known datatypes, including
  ones never referenced by the encoded terms; `seenDatatypes` records which of
  them are actually used. -/
  typeFactory : @Lambda.TypeFactory CoreLParams.IDMeta := #[]
  seenDatatypes : Std.HashSet String := {}
  datatypeFuns : Map String (Op.DatatypeFuncs × LConstr CoreLParams.IDMeta) := Map.empty
  /-- Global counter for generating unique bound variable names across all terms. -/
  bvCounter : Nat := 0
  /-- When true, always use `$__bv{N}` names for bound variables instead of
      human-readable names derived from user-provided names.
      Invariant during translation. -/
  uniqueBoundNames : Bool := false
  /-- When true, encode `Map` types/operations using the SMT Array theory
      (`select`/`store`) instead of an uninterpreted `Map` sort.
      Invariant during translation. -/
  useArrayTheory : Bool := false
deriving Repr, Inhabited

def SMT.Context.default : SMT.Context := {}

def SMT.Context.addSort (ctx : SMT.Context) (sort : Strata.DL.SMT.Sort) : SMT.Context :=
  { ctx with sorts := ctx.sorts.insert sort }

def SMT.Context.addUF (ctx : SMT.Context) (fn : UF) : SMT.Context :=
  { ctx with ufs := ctx.ufs.insert fn }

def SMT.Context.addIF (ctx : SMT.Context) (id : String) (args : List TermVar) (out : TermType) (body : Term) : SMT.Context :=
  { ctx with ifs := ctx.ifs.insert { id, args, out, body } }

def SMT.Context.addAxiom (ctx : SMT.Context) (axm : Term) : SMT.Context :=
  { ctx with axms := ctx.axms.insert axm }

/-- Commit a resolved function definition: emit its interpreted body (`addIF`)
    or uninterpreted declaration (`addUF`), followed by its axioms (`addAxiom`). -/
def SMT.Context.addResolvedFnDef (ctx : SMT.Context) (rdef : SMT.EncodedFnDef) : SMT.Context :=
  let ctx := match rdef.body? with
    | some body =>
      ctx.addIF rdef.id rdef.args rdef.out body
    | none =>
      let uf : UF := { id := rdef.id, args := rdef.args.map (·.ty), out := rdef.out }
      ctx.addUF uf
  rdef.axioms.foldl (init := ctx) (·.addAxiom ·)

/-- True if the function `uf`'s declaration has already been committed: it is
    in `ufs` (uninterpreted) or `ifs` (interpreted). -/
def SMT.Context.committedFn (ctx : SMT.Context) (uf : UF) : Bool :=
  ctx.ufs.contains uf || ctx.ifs.toArray.any (·.toUF == uf)

/-- True if the function `uf` is already committed in `ctx` or scheduled in the
    pending queue `pending`. Used to dedup function scheduling. -/
def SMT.Context.knowsFn (ctx : SMT.Context) (pending : List SMT.PendingFnDef) (uf : UF) : Bool :=
  ctx.committedFn uf || pending.any (·.uf == uf)

def SMT.Context.addSubst (ctx : SMT.Context) (newSubst: Map String TermType) : SMT.Context :=
  { ctx with tySubst := ctx.tySubst ++ newSubst }

def SMT.Context.restoreSubst (ctx : SMT.Context) (savedSubst: Map String TermType) : SMT.Context :=
  { ctx with tySubst := savedSubst }

def SMT.Context.hasDatatype (ctx : SMT.Context) (name : String) : Bool :=
  ctx.seenDatatypes.contains name

/-- Collect all sort, datatype, constructor, and selector names that have been
    pre-declared to the solver. Used to pre-populate the encoder's `usedNames`
    registry so that later UF/function encoding cannot collide with them. -/
def SMT.Context.preDeclaredNames (ctx : SMT.Context) : Std.HashSet String :=
  let sortNames := ctx.sorts.toArray.foldl (init := ({} : Std.HashSet String)) fun acc s => acc.insert s.name
  let dtNames := ctx.typeFactory.toList.foldl (init := sortNames) fun acc block =>
    block.foldl (init := acc) fun acc d =>
      if ctx.seenDatatypes.contains d.name then
        let acc := acc.insert d.name
        -- Include constructor and selector names emitted by declareDatatype
        d.constrs.foldl (init := acc) fun acc c =>
          let acc := acc.insert c.name.name
          c.args.foldl (init := acc) fun acc (fieldName, _) =>
            acc.insert (d.name ++ ".." ++ fieldName.name)
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
    let m := Map.union ctx.datatypeFuns (c.fmap (fun (_, x) => (.constructor, x)))
    let m := Map.union m (i.fmap (fun (_, x) => (.tester, x)))
    let m := Map.union m (s.fmap (fun (_, x) => (.selector, x)))
    let m := Map.union m (u.fmap (fun (_, x) => (.selector, x)))
    { ctx with seenDatatypes := ctx.seenDatatypes.insert d.name, datatypeFuns := m }

def SMT.Context.withTypeFactory (ctx : SMT.Context) (tf : @Lambda.TypeFactory CoreLParams.IDMeta) : SMT.Context :=
  { ctx with typeFactory := tf }

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
  | .tcons name args =>
    if name == "Map" && useArrayTheory then
      .constr "Array" (args.map $ lMonoTyToTermType useArrayTheory)
    else
      .constr name (args.map $ lMonoTyToTermType useArrayTheory)
  | .ftvar tv => .constr tv []

/-- Convert a datatype's constructors to typed SMT constructors. -/
private def datatypeConstructorsToSMT (d : LDatatype CoreLParams.IDMeta) (useArrayTheory : Bool := false): List SMTConstructor :=
  d.constrs.map fun c =>
    let fields := c.args.map fun (name, fieldTy) =>
      (d.name ++ ".." ++ name.name, lMonoTyToTermType useArrayTheory fieldTy)
    { name := c.name.name, args := fields }

/-- Ensures that all datatypes in the SMT encoding do not have arrow-typed
  constructor arguments-/
def validateDatatypesForSMT (typeFactory : @Lambda.TypeFactory CoreLParams.IDMeta)
    (seenDatatypes : Std.HashSet String) : Except Format Unit := do
  for block in typeFactory.toList do
    for d in block do
      if !seenDatatypes.contains d.name then continue
      for c in d.constrs do
        for (fieldName, fieldTy) in c.args do
          if fieldTy.containsArrow then
            throw f!"Cannot encode datatype '{d.name}' to SMT: \
                     constructor '{c.name.name}' has function-typed field '{fieldName.name}' of type '{fieldTy}'. \
                     Function types cannot be represented in SMT-LIB datatypes."

/--
Emit datatype declarations to the solver.
Uses the TypeFactory ordering (already topologically sorted).
Only emits datatypes that have been seen (added via addDatatype).
Single-element blocks use declare-datatype, multi-element blocks use declare-datatypes.
-/
def SMT.Context.emitDatatypes (ctx : SMT.Context) : Strata.SMT.SolverM Unit := do
  match validateDatatypesForSMT ctx.typeFactory ctx.seenDatatypes with
  | .error msg => throw (IO.userError (toString msg))
  | .ok () => pure ()
  for block in ctx.typeFactory.toList do
    let usedBlock := block.filter (fun d => ctx.seenDatatypes.contains d.name)
    match usedBlock with
    | [] => pure ()
    | [d] =>
      let constructors := datatypeConstructorsToSMT d ctx.useArrayTheory
      Strata.SMT.Solver.declareDatatype d.name d.typeArgs constructors
    | _ =>
      let dts := usedBlock.map fun d => (d.name, d.typeArgs, datatypeConstructorsToSMT d ctx.useArrayTheory)
      Strata.SMT.Solver.declareDatatypes dts

@[expose] abbrev BoundVars := List (String × TermType)

---------------------------------------------------------------------
partial def unifyTypes (typeVars : List String) (pattern : LMonoTy) (concrete : LMonoTy) (acc : Map String LMonoTy) : Map String LMonoTy :=
  match pattern, concrete with
  | .ftvar name, concrete_ty =>
    if typeVars.contains name then
      acc.insert name concrete_ty
    else acc
  | .tcons pname pargs, .tcons cname cargs =>
    if pname == cname && pargs.length == cargs.length then
      (pargs.zip cargs).foldl (fun acc' (p, c) => unifyTypes typeVars p c acc') acc
    else acc
  | _, _ => acc

def extractTypeInstantiations (typeVars : List String) (patterns : List LMonoTy) (concreteTypes : List LMonoTy) : Map String LMonoTy :=
  if patterns.length == concreteTypes.length then
    (patterns.zip concreteTypes).foldl (fun acc (pattern, concrete) =>
      unifyTypes typeVars pattern concrete acc) Map.empty
  else
    Map.empty


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
  -- Datatypes are looked up from the context's `typeFactory` (seeded by the
  -- caller from the env's datatypes); see `SMT.Context.typeFactory`.
  match ctx.typeFactory.getType id with
  | some d =>
    if ctx.hasDatatype id then ctx else
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
    ctx.addSort { name := id, arity := args.length }

mutual
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
    -- When using Array theory, convert Map to Array
    let id := if ctx.useArrayTheory then "Array" else "Map"
    let ctx := if ctx.useArrayTheory then ctx
               else SMT.Context.addType id args ctx
    let (args', ctx) ← LMonoTys.toSMTType args ctx
    .ok ((.constr id args'), ctx)
  | .tcons id args =>
    let ctx := SMT.Context.addType id args ctx
    let (args', ctx) ← LMonoTys.toSMTType args ctx
    .ok ((.constr id args'), ctx)
  | .ftvar tyv => match ctx.tySubst.find? tyv with
                    | .some termTy =>
                      .ok (termTy, ctx)
                    | _ => .error f!"Unimplemented encoding for type var {tyv}"

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

  | .trigger .EmptyTriggers | .trigger .EmptyGroup =>
    some (.app Op.triggers, .trigger, ctx)
  | .trigger .AddTrigger | .trigger .AddGroup =>
    some (Factory.addTriggerList, .trigger, ctx)

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

/-- Resolve a Core operator `fn` (of monomorphic type `fnty`) to its SMT builder.

    Returns the updated `SMT.Context` and pending-definition queue `pending`:
    for a user-defined factory function this only registers the `UF` and
    *appends* a `PendingFnDef` (deferring body/axiom encoding); the queue is
    threaded through term encoding and drained later by `drainPendingFnDefs`. -/
def toSMTOp (factory : @Lambda.Factory CoreLParams) (fn : CoreIdent) (fnty : LMonoTy) (ctx : SMT.Context)
  (pending : List SMT.PendingFnDef) :
  Except Format ((List Term → TermType → Term) × TermType × SMT.Context × List SMT.PendingFnDef) :=
  open LTy.Syntax in do
  -- Encode the type to ensure any datatypes are registered in the context
  let tys := LMonoTy.destructArrow fnty
  let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
  let intys := tys.take (tys.length - 1)
  -- Need to encode arg types also (e.g. for testers)
  let ctx := match LMonoTys.toSMTType intys ctx with
    | .ok (_, ctx') => ctx'
    | .error _ => ctx
  let (smt_outty, ctx) ← LMonoTy.toSMTType outty ctx

  match ctx.datatypeFuns.find? fn.name with
  | some (kind, c) =>
    let adtApp := fun (args : List Term) (retty : TermType) =>
        /-
        Note: testers use constructor, translated in `Op.mkName` to is-foo
        Selectors use full function name (Datatype..fieldName) for uniqueness.
        Unsafe selectors (e.g. List..head!) use the safe name (List..head).
        -/
        let name := match kind with
          | .selector => stripUnsafeDestructorSuffix fn.name
          | _ => c.name.name
        Term.app (.datatype_op kind name) args retty
    .ok (adtApp, smt_outty, ctx, pending)
  | none =>
    -- Not a constructor, tester, or destructor
    match factory[fn.name]? with
    | none => .error f!"Cannot find function {fn} in Strata Core's Factory!"
    | some func =>
      match corePredefinedOpToSMTOp (CoreOp.ofString func.name.name) ctx with
      | some (op, retty, ctx) => .ok (op, retty, ctx, pending)
      | none => do
      let fnname := func.name.name
      if (fnname == "select" || fnname == "update") && ctx.useArrayTheory then
        .ok (.app (if fnname == "select" then Op.select else Op.store), smt_outty, ctx, pending)
      else
        let formals := func.inputs.keys
        let formalStrs := formals.map (toString ∘ format)
        let tys := LMonoTy.destructArrow fnty
        let intys := tys.take (tys.length - 1)
        let (smt_intys, ctx) ← LMonoTys.toSMTType intys ctx
        let bvs := formalStrs.zip smt_intys
        let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
        let (smt_outty, ctx) ← LMonoTy.toSMTType outty ctx
        let uf : UF := { id := (toString $ format fn), args := smt_intys, out := smt_outty }
        let arrowParams := func.inputs.toList.filter (fun (_, ty) => ty.containsArrow)
        if !arrowParams.isEmpty then
          let names := arrowParams.map (fun (n, _) => toString (format n))
          .error f!"Cannot encode function '{func.name}' to SMT: \
                    it has function-typed parameter(s) {names}. \
                    Higher-order functions cannot be encoded to SMT. \
                    Consider marking the function as `inline`."
        else if func.output.containsArrow then
          .error f!"Cannot encode function '{func.name}' to SMT: \
                    it returns a function type '{func.output}'. \
                    Higher-order functions cannot be encoded to SMT. \
                    Consider marking the function as `inline`."
        -- Note: hasAbs does not special-case directly-applied lambdas (let expressions)
        -- because the partial evaluator beta-reduces those before SMT encoding.
        else if func.body.any LExpr.hasAbs then
          .error f!"Cannot encode function '{func.name}' to SMT: \
                    its body contains a lambda expression. \
                    Lambda abstractions cannot be encoded to SMT. \
                    Consider marking the function as `inline`."
        else
          -- Defer encoding the function's definition (interpreted body and/or
          -- axioms). Those would require calling `toSMTTerm` on expressions
          -- drawn from the factory; append a `PendingFnDef` to the queue instead.
          let pending := if ctx.knowsFn pending uf then pending
            else pending ++ [{ fn := fn, uf := uf, fnty := fnty, tySubst := ctx.tySubst }]
          .ok (.app (Op.uf uf), smt_outty, ctx, pending)

mutual

@[expose]
def toSMTTerm (factory : @Lambda.Factory CoreLParams) (bvs : BoundVars) (e : LExpr CoreLParams.mono) (ctx : SMT.Context)
  (pending : List SMT.PendingFnDef)
  : Except Format (Term × SMT.Context × List SMT.PendingFnDef) := do
  match e with
  | .boolConst _ b => .ok (Term.bool b, ctx, pending)
  | .intConst _ i => .ok (Term.int i, ctx, pending)
  | .realConst _ r =>
    match StrataDDM.Decimal.fromRat r with
    | some d => .ok (Term.real d, ctx, pending)
    | none => .error f!"Non-decimal real value {e}"
  | .bitvecConst _ n b => .ok (Term.bitvec b, ctx, pending)
  | .strConst _ s => .ok (Term.string s, ctx, pending)
  | .op _ fn fnty =>
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}."
    | some fnty =>
      -- 0-ary Operation.
      let (op, retty, ctx, pending) ← toSMTOp factory fn fnty ctx pending
      .ok (op [] retty, ctx, pending)

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
      let (tty, ctx) ← LMonoTy.toSMTType ty ctx
      let uf := { id := f.name, args := [], out := tty }
      .ok (.app (.uf uf) [] tty, ctx.addUF uf, pending)

  | .abs _ _ _ _ =>
    .error f!"Cannot encode lambda expression to SMT. \
              Lambda abstractions must be eliminated (e.g., by beta-reduction) \
              before SMT encoding.\n\
              Lambda: {e}"

  | .quant _ _ _ .none _ _ => .error f!"Cannot encode untyped quantifier {e}"
  | .quant _ qk name (.some ty) tr e =>
    let fvarNames := (e.collectFvarNames.map (·.name)).toArray
    -- Generate base name using global counter to ensure uniqueness across terms.
    -- The `$__` prefix is reserved for internal use and cannot appear in user
    -- identifiers.
    let (baseName, startSuffix) :=
      if ctx.uniqueBoundNames || name.isEmpty then
        (s!"$__bv{ctx.bvCounter}", 1)
      else
        let (b, s) := Strata.Name.breakDisambiguated name
        (Encoder.sanitizeSmtName b, s)
    let ctx := { ctx with bvCounter := ctx.bvCounter + 1 }
    -- Check for clashes with existing bvars, fvars, sorts, datatypes, and fvars in body
    let usedNames := Std.HashSet.ofList (bvs.map (·.1) ++ ctx.ufs.toList.map (·.id) ++ fvarNames.toList
      ++ ctx.sorts.toList.map (·.name) ++ ctx.seenDatatypes.toList)
    let x := Strata.Name.findUnique baseName startSuffix usedNames
    let (ety, ctx) ← LMonoTy.toSMTType ty ctx
    -- The trigger is usually an application (the pattern to match on), but for
    -- quantifiers without an explicit trigger it is `LExpr.noTrigger` (a bare
    -- `.bvar`), which `Factory.quant` treats as "no meaningful trigger". Encode
    -- applications via `appToSMTTerm` and anything else (e.g. the no-trigger
    -- bvar) via `toSMTTerm`.
    let (trt, ctx, pending) ← match tr with
      | .app _ fn arg => appToSMTTerm factory ((x, ety) :: bvs) fn arg [] ctx pending
      | tr' => toSMTTerm factory ((x, ety) :: bvs) tr' ctx pending
    let (et, ctx, pending) ← toSMTTerm factory ((x, ety) :: bvs) e ctx pending
    .ok (Factory.quant (convertQuantifierKind qk) x ety trt et, ctx, pending)
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
  (pending : List SMT.PendingFnDef) :
  Except Format (Term × SMT.Context × List SMT.PendingFnDef) := do
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
                          Original expression: {(LExpr.app () fn arg).eraseTypes}"
    | _, _ => .error f!"Natural numbers expected as indices for re.loop.\n\
                        Original expression: {(LExpr.app () fn arg).eraseTypes}"

  | .app _ fn' e1, e2 => do
    let (e2t, ctx, pending) ← toSMTTerm factory bvs e2 ctx pending
    appToSMTTerm factory bvs fn' e1 (e2t :: acc) ctx pending

  | .op _ fn fnty, e1 => do
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}. \n\
                        Appears in expression: {LExpr.app () (LExpr.op () fn fnty) e1}"
    | some fnty =>
      let (op, retty, ctx, pending) ← toSMTOp factory fn fnty ctx pending
      let (e1t, ctx, pending) ← toSMTTerm factory bvs e1 ctx pending
      .ok (op (e1t :: acc) retty, ctx, pending)
  | .fvar _ fn (.some fnty), e1 => do
    let tys := LMonoTy.destructArrow fnty
    let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
    let intys := tys.take (tys.length - 1)
    let (smt_outty, ctx) ← LMonoTy.toSMTType outty ctx
    let (e1t, ctx, pending) ← toSMTTerm factory bvs e1 ctx pending
    let allArgs := e1t :: acc
    let mut argTysRev : List TermType := []
    let mut ctx := ctx
    for inty in intys do
      let (smt_inty, ctx') ← LMonoTy.toSMTType inty ctx
      ctx := ctx'
      argTysRev := smt_inty :: argTysRev
    let argTys := argTysRev.reverse
    let uf := UF.mk (id := (toString $ format fn)) (args := argTys) (out := smt_outty)
    .ok (Term.app (.uf uf) allArgs smt_outty, ctx, pending)
  | _, _ =>
    .error f!"Cannot encode .app expression {LExpr.app () fn arg}"
termination_by (sizeOf fn + sizeOf arg, 0)
decreasing_by
  all_goals simp_wf
  all_goals (first | omega | term_by_mem)

end

/--
Encode a single deferred function `p`: encode its interpreted body (if any) and
its axioms to SMT `Term`s, returning the resolved
definition together with the (further) functions those terms reference.
-/
def resolveOnePendingFnDef (factory : @Lambda.Factory CoreLParams)
    (ctx : SMT.Context) (p : SMT.PendingFnDef) :
    Except Format (SMT.EncodedFnDef × SMT.Context × List SMT.PendingFnDef) :=
  open LTy.Syntax in do
  let some func := factory[p.fn.name]?
    | .error f!"Cannot find function {p.fn} in Strata Core's Factory!"

  let tys := LMonoTy.destructArrow p.fnty
  let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty p.fnty)
  let intys := tys.take (tys.length - 1)
  let formals := func.inputs.keys
  let formalStrs := formals.map (toString ∘ format)

  -- Seed the encoder's type substitution with the snapshot captured at the
  -- point this function was referenced, so type variables appearing in `p.fnty`
  -- (when the referrer was polymorphic) resolve while encoding its definition.
  let savedSubst := ctx.tySubst
  let ctx := ctx.addSubst p.tySubst
  let seededSubst := ctx.tySubst
  -- Encode arg types (needed for both interpreted and uninterpreted paths).
  let (smt_intys, ctx) ← LMonoTys.toSMTType intys ctx
  let args := formalStrs.zip smt_intys |>.map fun (n, ty) => ({ id := n, ty } : TermVar)
  -- Encode the body (interpreted functions) or leave it uninterpreted.
  let (body?, ctx, pending) ←
    if func.isRecursive then
      .ok (none, ctx, ([] : List SMT.PendingFnDef))
    else match func.body with
    | none => .ok (none, ctx, ([] : List SMT.PendingFnDef))
    | some body =>
      -- Substitute the formals in the function body with appropriate `.bvar`s.
      -- Use substFvarsLifting to properly lift indices under binders.
      let bvs := args.map fun v => (v.id, v.ty)
      let bvars := (List.range formals.length).map (fun i => LExpr.bvar () i)
      let body := LExpr.substFvarsLifting body (formals.zip bvars)
      let (term, ctx, pending) ← toSMTTerm factory bvs body ctx []
      .ok (some term, ctx, pending)

  -- Encode the function's axioms (recursive-function axioms are pre-computed by
  -- `Core.generateRecursiveAxioms` and carried in `func.axioms`).
  let allPatterns := func.inputs.values ++ [func.output]
  let type_instantiations : Map String LMonoTy :=
    extractTypeInstantiations func.typeArgs allPatterns (intys ++ [outty])
  let smt_ty_inst ← type_instantiations.foldlM (fun acc_map (tyVar, monoTy) => do
    let (smtTy, _) ← LMonoTy.toSMTType monoTy ctx
    .ok (acc_map.insert tyVar smtTy)) Map.empty

  let (axiomTermsRev, ctx, pending) ← func.axioms.foldlM
    (init := (([] : List Term), ctx, pending))
    (fun (axs, ctx, pending) (ax : LExpr CoreLParams.mono) => do
      let (axiom_term, ctx, pending) ←
        toSMTTerm factory [] ax (ctx.addSubst smt_ty_inst) pending
      .ok (axiom_term :: axs, ctx.restoreSubst seededSubst, pending))
  -- Restore the substitution that was active before this function.
  .ok ({ id := p.uf.id, args, out := p.uf.out, body?, axioms := axiomTermsRev.reverse },
       ctx.restoreSubst savedSubst, pending)

/--
Resolve and commit the transitive closure of deferred function definitions
to `SMT.Context`.
The fuel is set to factory.toArray.size + pending.length, which is enough to
visit all bodies and axioms. It is used to make the termination proof easier.
-/
def processPendingFnDefsAux (factory : @Lambda.Factory CoreLParams) (fuel : Nat)
    (ctx : SMT.Context) (seen : List UF)
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
        let seen := p.uf :: seen
        let (rdef, ctx, deps) ← resolveOnePendingFnDef factory ctx p
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
    (ctx : SMT.Context) (pending : List SMT.PendingFnDef) : Except Format SMT.Context :=
  processPendingFnDefsAux factory (factory.toArray.size + pending.length) ctx [] pending

def toSMTTerms (factory : @Lambda.Factory CoreLParams) (es : List (LExpr CoreLParams.mono)) (ctx : SMT.Context)
  (pending : List SMT.PendingFnDef) :
  Except Format ((List Term) × SMT.Context × List SMT.PendingFnDef) := do
  match es with
  | [] => .ok ([], ctx, pending)
  | e :: erest =>
    let (et, ctx, pending) ← toSMTTerm factory [] e ctx pending
    let (erestt, ctx, pending) ← toSMTTerms factory erest ctx pending
    .ok ((et :: erestt), ctx, pending)

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

/--
Encode a proof obligation into SMT terms: path conditions (P) and obligation (Q).
The obligation Q is returned without negation; see `encodeCore` in Verifier.lean
for the check-sat encoding that applies negation for validity checks.

Variable definitions (from `init name ty (.det e)`) are returned separately as
`VarDefinition`s so the caller can emit them as `define-fun`.
Variable declarations (from `init name ty .nondet`) are returned separately as
`VarDeclaration`s so the caller can emit them as `declare-fun`.
-/
def ProofObligation.toSMTTerms (factory : @Lambda.Factory CoreLParams)
  (d : Imperative.ProofObligation Expression) (ctx : SMT.Context := SMT.Context.default) :
  Except Format (List Term × List VarDefinition × List VarDeclaration × Term × SMT.Context × Statistics) := do
  -- 1. Partition the (flattened) path-condition entries by kind: plain
  --    assumptions, variable definitions/declarations, and distinctness facts
  --    (all of which now live as path-condition entries).
  let flatEntries := d.assumptions.flatten
  let mut assumptionExprsRev : List (LExpr CoreLParams.mono) := []
  let mut varDefsRev : List (CoreIdent × Expression.Ty × LExpr CoreLParams.mono) := []
  let mut varDeclsRev : List (CoreIdent × Expression.Ty) := []
  let mut distinctGroupsRev : List (List (LExpr CoreLParams.mono)) := []
  for entry in flatEntries do
    match entry with
    | .assumption _ expr => assumptionExprsRev := expr :: assumptionExprsRev
    | .varDecl name ty (.det e) => varDefsRev := (name, ty, e) :: varDefsRev
    | .varDecl name ty .nondet => varDeclsRev := (name, ty) :: varDeclsRev
    | .distinct _ exprs => distinctGroupsRev := exprs :: distinctGroupsRev
  let assumptionExprs := assumptionExprsRev.reverse
  let varDefs := varDefsRev.reverse
  let varDecls := varDeclsRev.reverse
  let distinctGroups := distinctGroupsRev.reverse

  -- `pending` accumulates factory functions whose definitions `toSMTOp` defers;
  -- it is threaded through all term encoding below and drained once at the end.
  let pending : List SMT.PendingFnDef := []

  -- 2. Encode distinctness facts, one `distinct` assertion per group.
  let (ctx, pending, distinct_terms) ← distinctGroups.foldlM (λ (ctx, pending, tss) es =>
    do let (ts, ctx', pending') ← Core.toSMTTerms factory es ctx pending
       pure (ctx', pending', ts :: tss)) (ctx, pending, [])
  let distinct_assumptions := distinct_terms.reverse.map
    (λ ts => Term.app (.core .distinct) ts .bool)

  -- 3. Encode assumptions.
  let (assumptions_terms, ctx, pending) ← Core.toSMTTerms factory assumptionExprs ctx pending

  -- 4. Encode variable definitions (`init name ty (.det e)`), emitted by the
  --    caller as `define-fun`.
  let (smtVarDefsRev, ctx, pending) ← varDefs.foldlM (init := (([] : List VarDefinition), ctx, pending)) fun (defs, ctx, pending) (name, ty, rhs) => do
    if h : ty.isMonoType then
      let (smtTy, ctx) ← LMonoTy.toSMTType (ty.toMonoType h) ctx
      let (rhsTerm, ctx, pending) ← Core.toSMTTerm factory [] rhs ctx pending
      .ok ({ name := name.name, ty := smtTy, body := rhsTerm } :: defs, ctx, pending)
    else
      .error f!"SMT encoding: variable definition '{name.name}' has non-monomorphic type"
  let smtVarDefs := smtVarDefsRev.reverse

  -- 5. Encode variable declarations, emitted by the
  --    caller as `declare-fun`. These have no body, so they schedule no
  --    deferred functions and need not thread `pending`.
  let (smtVarDeclsRev, ctx) ← varDecls.foldlM (init := (([] : List VarDeclaration), ctx)) fun (decls, ctx) (name, ty) => do
    if h : ty.isMonoType then
      let (smtTy, ctx) ← LMonoTy.toSMTType (ty.toMonoType h) ctx
      .ok ({ name := name.name, ty := smtTy } :: decls, ctx)
    else
      .error f!"SMT encoding: variable declaration '{name.name}' has non-monomorphic type"
  let smtVarDecls := smtVarDeclsRev.reverse

  -- 6. Encode the obligation (the goal) itself.
  let (obligation_term, ctx, pending) ← Core.toSMTTerm factory [] d.obligation ctx pending

  -- 7. Resolve and commit the definitions/axioms of every factory function
  --    referenced above. `toSMTOp` defers these into `pending`; commit them now
  --    that all terms (distinctness facts, assumptions, var defs, and the
  --    obligation) have been encoded.
  let ctx ← processPendingFnDefs factory ctx pending

  -- 8. Collect statistics and return the encoded pieces.
  let stats : Statistics := ({} : Statistics)
    |>.increment s!"{Evaluator.Stats.smtProofObligation_numAssumptions}"
        (distinct_assumptions.length + assumptions_terms.length)
  .ok (distinct_assumptions ++ assumptions_terms, smtVarDefs, smtVarDecls, obligation_term, ctx, stats)

---------------------------------------------------------------------

/-- Convert an expression of type LExpr to a String representation in SMT-Lib syntax, for testing.
    Outputs variable declarations followed by the assertion of the encoded term. -/
def toSMTCommandsWithAssert (e : LExpr CoreLParams.mono)
  (factory : @Lambda.Factory CoreLParams := Core.Factory) (ctx : SMT.Context := SMT.Context.default)
  : IO String := do
  let smtctx := toSMTTerm factory [] e ctx []
  match smtctx with
  | .error e => return e.pretty
  | .ok (smt, _, _) =>
    let b ← IO.mkRef { : IO.FS.Stream.Buffer }
    let solver ← Solver.bufferWriter b
    let ((enc, _), _) ← ((Encoder.encodeTerm smt).run EncoderState.init).run solver
    let _ ← (Solver.assert enc).run solver
    let contents ← b.get
    if h: contents.data.IsValidUTF8
    then return String.fromUTF8 contents.data h
    else return "Converting SMT Term to bytes produced an invalid UTF-8 sequence."

/--
Convert an `SMT.Term` back to a Core `LExpr` (best-effort, partial inverse of `toSMTTerm`).

Handles:
- Primitives: bool, int, real, bitvec, string
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
  | .prim (.bool b)       => .boolConst () b
  | .prim (.int i)        => .intConst () i
  | .prim (.real d)       => .realConst () d.toRat
  | .prim (.bitvec b)     => .bitvecConst () _ b
  | .prim (.string s)     => .strConst () s
  | .var v                =>
    -- Zero-arg constructors arrive as plain variables from the SMT solver.
    -- Mark them with `.op` so the formatter can emit `Name()`.
    if constructorNames.contains v.id then
      .op () v.id none
    else
      .fvar () v.id none
  | .app (.core (.uf uf)) args _retTy =>
    -- Constructor names use `.op` so the formatter can distinguish them
    -- from plain variables (e.g., `Nil` constructor must not be .fvar)
    let fnExpr : LExpr CoreLParams.mono :=
      if constructorNames.contains uf.id then
        .op () uf.id none
      else
        .fvar () uf.id none
    args.foldl (fun acc arg => .app () acc (smtTermToLExpr arg constructorNames)) fnExpr
  | .app (.datatype_op _kind name) args _retTy =>
    let fnExpr : LExpr CoreLParams.mono := .op () name none
    args.foldl (fun acc arg => .app () acc (smtTermToLExpr arg constructorNames)) fnExpr
  | .app op args _ =>
    -- Generic fallback for other ops: render as op name applied to args
    let opName := op.mkName
    let fnExpr : LExpr CoreLParams.mono := .op () opName none
    args.foldl (fun acc arg => .app () acc (smtTermToLExpr arg constructorNames)) fnExpr
  | .none _ty             => .op () "none" none
  | .some inner           => .app () (.op () "some" none) (smtTermToLExpr inner constructorNames)
  | .quant _ _ _ _        =>
    -- Quantifiers in model values are unusual; fall back to string repr
    let s := match Strata.SMTDDM.termToString t with
             | .ok s => s | .error _ => repr t |>.pretty
    .fvar () s none

/--
Extract the set of datatype constructor names from an `SMT.Context`.
-/
def SMT.Context.getConstructorNames (ctx : SMT.Context) : Std.HashSet String :=
  ctx.datatypeFuns.toList.foldl (init := {}) fun acc (name, (kind, _)) =>
    if kind == .constructor then acc.insert name else acc

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

end -- public section

end Core
