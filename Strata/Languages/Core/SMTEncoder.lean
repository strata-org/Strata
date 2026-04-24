/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Core
public import Strata.DL.SMT.SMT
public import Strata.DL.Imperative.SMTUtils
public import Strata.DL.Lambda.RecursiveAxioms
import Init.Data.String.Extra
public import Strata.DDM.Util.DecimalRat
import Strata.DL.Imperative.SMTUtils
public import Strata.Languages.Core.CoreOp

---------------------------------------------------------------------

namespace Core
open Std (ToFormat Format format)
open Lambda Strata.SMT Strata.SMT.Encoder

public section

structure SMT.IF where
  uf : UF
  body : Term
deriving Repr, DecidableEq, Inhabited

structure SMT.Sort where
  name : String
  arity : Nat
deriving Repr, DecidableEq, Inhabited

-- (FIXME) Can/should we use Strata.SMT.EncoderState here directly?
structure SMT.Context where
  sorts : Array SMT.Sort := #[]
  ufs : Array UF := #[]
  ifs : Array SMT.IF := #[]
  axms : Array Term := #[]
  tySubst: Map String TermType := []
  /-- Stores the TypeFactory purely for ordering datatype declarations
  correctly (TypeFactory in topological order) -/
  typeFactory : @Lambda.TypeFactory CoreLParams.IDMeta := #[]
  seenDatatypes : Std.HashSet String := {}
  datatypeFuns : Map String (Op.DatatypeFuncs × LConstr CoreLParams.IDMeta) := Map.empty
  /-- Global counter for generating unique bound variable names across all terms. -/
  bvCounter : Nat := 0
  /-- When true, always use `$__bv{N}` names for bound variables instead of
      human-readable names derived from user-provided names. -/
  uniqueBoundNames : Bool := false
deriving Repr, Inhabited

def SMT.Context.default : SMT.Context := {}

def SMT.Context.addSort (ctx : SMT.Context) (sort : SMT.Sort) : SMT.Context :=
  if sort ∈ ctx.sorts then ctx else
  { ctx with sorts := ctx.sorts.push sort }

def SMT.Context.addUF (ctx : SMT.Context) (fn : UF) : SMT.Context :=
  if fn ∈ ctx.ufs then ctx else
  { ctx with ufs := ctx.ufs.push fn }

def SMT.Context.addIF (ctx : SMT.Context) (fn : UF) (body : Term) : SMT.Context :=
  let smtif := { uf := fn, body := body }
  if smtif ∈ ctx.ifs then ctx else
  { ctx with ifs := ctx.ifs.push smtif }

def SMT.Context.addAxiom (ctx : SMT.Context) (axm : Term) : SMT.Context :=
  if axm ∈ ctx.axms then ctx else
  { ctx with axms := ctx.axms.push axm }

def SMT.Context.addSubst (ctx : SMT.Context) (newSubst: Map String TermType) : SMT.Context :=
  { ctx with tySubst := ctx.tySubst ++ newSubst }

def SMT.Context.restoreSubst (ctx : SMT.Context) (savedSubst: Map String TermType) : SMT.Context :=
  { ctx with tySubst := savedSubst }

def SMT.Context.hasDatatype (ctx : SMT.Context) (name : String) : Bool :=
  ctx.seenDatatypes.contains name

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
def lMonoTyToTermType (ty : LMonoTy) : TermType :=
  match ty with
  | .bitvec n => .bitvec n
  | .tcons "bool" [] => .bool
  | .tcons "int" [] => .int
  | .tcons "real" [] => .real
  | .tcons "string" [] => .string
  | .tcons "regex" [] => .regex
  | .tcons name args => .constr name (args.map lMonoTyToTermType)
  | .ftvar tv => .constr tv []

/-- Convert a datatype's constructors to typed SMT constructors. -/
private def datatypeConstructorsToSMT (d : LDatatype CoreLParams.IDMeta) : List SMTConstructor :=
  d.constrs.map fun c =>
    let fields := c.args.map fun (name, fieldTy) =>
      (d.name ++ ".." ++ name.name, lMonoTyToTermType fieldTy)
    { name := c.name.name, args := fields }

/--
Emit datatype declarations to the solver.
Uses the TypeFactory ordering (already topologically sorted).
Only emits datatypes that have been seen (added via addDatatype).
Single-element blocks use declare-datatype, multi-element blocks use declare-datatypes.
-/
def SMT.Context.emitDatatypes (ctx : SMT.Context) : Strata.SMT.SolverM Unit := do
  for block in ctx.typeFactory.toList do
    let usedBlock := block.filter (fun d => ctx.seenDatatypes.contains d.name)
    match usedBlock with
    | [] => pure ()
    | [d] =>
      let constructors := datatypeConstructorsToSMT d
      Strata.SMT.Solver.declareDatatype d.name d.typeArgs constructors
    | _ =>
      let dts := usedBlock.map fun d => (d.name, d.typeArgs, datatypeConstructorsToSMT d)
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
partial def SMT.Context.addType (E: Env) (id: String) (args: List LMonoTy) (ctx: SMT.Context) :
  SMT.Context :=
  -- Always recurse into concrete args to register any type references
  let ctx := args.foldl (fun ctx arg =>
    match arg with
    | .tcons id1 args1 =>
      if isBuiltinCoreTy id1 then ctx
      else SMT.Context.addType E id1 args1 ctx
    | _ => ctx) ctx
  match E.datatypes.getType id with
  | some d =>
    if ctx.hasDatatype id then ctx else
    let ctx := ctx.addDatatype d
    d.constrs.foldl (fun (ctx : SMT.Context) c =>
      c.args.foldl (fun (ctx: SMT.Context) (_, t) =>
        match t with
        | .bool | .int | .real | .string | .tcons "regex" [] => ctx
        | .tcons id1 args1 => SMT.Context.addType E id1 args1 ctx
        | _ => ctx
        ) ctx
      ) ctx
  | none =>
    ctx.addSort { name := id, arity := args.length }

mutual
def LMonoTy.toSMTType (E: Env) (ty : LMonoTy) (ctx : SMT.Context) (useArrayTheory : Bool := false) :
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
    let id := if useArrayTheory then "Array" else "Map"
    let ctx := if useArrayTheory then ctx
               else SMT.Context.addType E id args ctx
    let (args', ctx) ← LMonoTys.toSMTType E args ctx useArrayTheory
    .ok ((.constr id args'), ctx)
  | .tcons id args =>
    let ctx := SMT.Context.addType E id args ctx
    let (args', ctx) ← LMonoTys.toSMTType E args ctx useArrayTheory
    .ok ((.constr id args'), ctx)
  | .ftvar tyv => match ctx.tySubst.find? tyv with
                    | .some termTy =>
                      .ok (termTy, ctx)
                    | _ => .error f!"Unimplemented encoding for type var {tyv}"

def LMonoTys.toSMTType (E: Env) (args : LMonoTys) (ctx : SMT.Context) (useArrayTheory : Bool := false) :
    Except Format ((List TermType) × SMT.Context) := do
  match args with
  | [] => .ok ([], ctx)
  | t :: trest =>
    let (t', ctx) ← LMonoTy.toSMTType E t ctx useArrayTheory
    let (trest', ctx) ← LMonoTys.toSMTType E trest ctx useArrayTheory
    .ok ((t' :: trest'), ctx)
end

def convertQuantifierKind : Lambda.QuantifierKind -> Strata.SMT.QuantifierKind
  | .all => .all
  | .exist => .exist

mutual

@[expose]
partial def toSMTTerm (E : Env) (bvs : BoundVars) (e : LExpr CoreLParams.mono) (ctx : SMT.Context)
  (useArrayTheory : Bool := false)
  : Except Format (Term × SMT.Context) := do
  match e with
  | .boolConst _ b => .ok (Term.bool b, ctx)
  | .intConst _ i => .ok (Term.int i, ctx)
  | .realConst _ r =>
    match Strata.Decimal.fromRat r with
    | some d => .ok (Term.real d, ctx)
    | none => .error f!"Non-decimal real value {e}"
  | .bitvecConst _ n b => .ok (Term.bitvec b, ctx)
  | .strConst _ s => .ok (Term.string s, ctx)
  | .op _ fn fnty =>
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}."
    | some fnty =>
      -- 0-ary Operation.
      let (op, retty, ctx) ← toSMTOp E fn fnty ctx useArrayTheory
      .ok (op [] retty, ctx)

  | .bvar _ i =>
    if h: i < bvs.length
    then do
      let var := bvs[i]
      .ok ((TermVar.mk var.fst var.snd), ctx)
    else .error f!"Bound variable index is out of bounds: {i}"

  | .fvar _ f ty =>
    match ty with
    | none => .error f!"Cannot encode unannotated free variable {e}"
    | some ty =>
      let (tty, ctx) ← LMonoTy.toSMTType E ty ctx useArrayTheory
      let uf := { id := f.name, args := [], out := tty }
      .ok (.app (.uf uf) [] tty, ctx.addUF uf)

  | .abs _ _ ty e => .error f!"Cannot encode lambda abstraction {e}"

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
    -- Check for clashes with existing bvars, fvars in ctx, and fvars in body
    let usedNames := Std.HashSet.ofList (bvs.map (·.1) ++ ctx.ufs.toList.map (·.id) ++ fvarNames.toList)
    let x := Strata.Name.findUnique baseName startSuffix usedNames
    let (ety, ctx) ← LMonoTy.toSMTType E ty ctx useArrayTheory
    let (trt, ctx) ← appToSMTTerm E ((x, ety) :: bvs) tr [] ctx useArrayTheory
    let (et, ctx) ← toSMTTerm E ((x, ety) :: bvs) e ctx useArrayTheory
    .ok (Factory.quant (convertQuantifierKind qk) x ety trt et, ctx)
  | .eq _ e1 e2 =>
    let (e1t, ctx) ← toSMTTerm E bvs e1 ctx useArrayTheory
    let (e2t, ctx) ← toSMTTerm E bvs e2 ctx useArrayTheory
    .ok ((Factory.eq e1t e2t), ctx)

  | .ite _ c t f =>
    let (ct, ctx) ← toSMTTerm E bvs c ctx useArrayTheory
    let (tt, ctx) ← toSMTTerm E bvs t ctx useArrayTheory
    let (ft, ctx) ← toSMTTerm E bvs f ctx useArrayTheory
    .ok ((Factory.ite ct tt ft), ctx)

  | .app _ _ _ =>
    appToSMTTerm E bvs e [] ctx useArrayTheory

partial def appToSMTTerm (E : Env) (bvs : BoundVars) (e : LExpr CoreLParams.mono) (acc : List Term) (ctx : SMT.Context)
  (useArrayTheory : Bool := false) :
  Except Format (Term × SMT.Context) := do
  match e with
  -- Special case for indexed SMT operations.
  | .app _ (.app _ (.app _ (.op _ "Re.Loop" _) x) n1) n2 =>
    let (xt, ctx) ← toSMTTerm E bvs x ctx useArrayTheory
    match Lambda.LExpr.denoteInt n1, Lambda.LExpr.denoteInt n2 with
    | .some n1i, .some n2i =>
      match Int.toNat? n1i, Int.toNat? n2i with
      | .some n1n, .some n2n =>
        .ok (.app (Op.re_loop n1n n2n) [xt] .regex, ctx)
      | _, _ => .error f!"Natural numbers expected as indices for re.loop.\n\
                          Original expression: {e.eraseTypes}"
    | _, _ => .error f!"Natural numbers expected as indices for re.loop.\n\
                        Original expression: {e.eraseTypes}"

  | .app _ (.app m fn e1) e2 => do
    match e1, e2 with
    | _, _ =>
      let (e2t, ctx) ← toSMTTerm E bvs e2 ctx useArrayTheory
      appToSMTTerm E bvs (.app m fn e1) (e2t :: acc) ctx useArrayTheory

  | .app _ (.op _ fn fnty) e1 => do
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}. \n\
                        Appears in expression: {e}"
    | some fnty =>
      let (op, retty, ctx) ← toSMTOp E fn fnty ctx useArrayTheory
      let (e1t, ctx) ← toSMTTerm E bvs e1 ctx useArrayTheory
      .ok (op (e1t :: acc) retty, ctx)
  | .app _ (.fvar _ fn (.some fnty)) e1 => do
    let tys := LMonoTy.destructArrow fnty
    let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
    let intys := tys.take (tys.length - 1)
    let (smt_outty, ctx) ← LMonoTy.toSMTType E outty ctx useArrayTheory
    let (e1t, ctx) ← toSMTTerm E bvs e1 ctx useArrayTheory
    let allArgs := e1t :: acc
    let mut argvars : List TermVar := []
    let mut ctx := ctx
    for inty in intys do
      let (smt_inty, ctx') ← LMonoTy.toSMTType E inty ctx useArrayTheory
      ctx := ctx'
      argvars := argvars ++ [TermVar.mk (toString $ format inty) smt_inty]
    let uf := UF.mk (id := (toString $ format fn)) (args := argvars) (out := smt_outty)
    .ok (Term.app (.uf uf) allArgs smt_outty, ctx)
  | .app _ _ _ =>
    .error f!"Cannot encode expression {e}"

  | _ => toSMTTerm E bvs e ctx useArrayTheory

partial def toSMTOp (E : Env) (fn : CoreIdent) (fnty : LMonoTy) (ctx : SMT.Context)
  (useArrayTheory : Bool := false) :
  Except Format ((List Term → TermType → Term) × TermType × SMT.Context) :=
  open LTy.Syntax in do
  -- Encode the type to ensure any datatypes are registered in the context
  let tys := LMonoTy.destructArrow fnty
  let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
  let intys := tys.take (tys.length - 1)
  -- Need to encode arg types also (e.g. for testers)
  let ctx := match LMonoTys.toSMTType E intys ctx useArrayTheory with
    | .ok (_, ctx') => ctx'
    | .error _ => ctx
  let (smt_outty, ctx) ← LMonoTy.toSMTType E outty ctx useArrayTheory

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
    .ok (adtApp, smt_outty, ctx)
  | none =>
    -- Not a constructor, tester, or destructor
    -- Helper: SDivOverflow(x, y) = (x == INT_MIN) ∧ (y == -1)
    let sdivOverflowEnc := fun (n : Nat) (ctx : SMT.Context) =>
      let sdivOverflowApp := fun (args : List Term) (_retTy : TermType) =>
        match args with
        | [x, y] =>
          let intMin := Term.prim (.bitvec (BitVec.intMin n))
          let negOne := Term.prim (.bitvec (BitVec.allOnes n))
          let xIsMin := Term.app Op.eq [x, intMin] .bool
          let yIsNegOne := Term.app Op.eq [y, negOne] .bool
          Term.app Op.and [xIsMin, yIsNegOne] .bool
        | _ => Term.app Op.and [] .bool
      Except.ok (sdivOverflowApp, TermType.prim .bool, ctx)
    -- USubOverflow(x, y) = bvult(x, y)
    let usubOverflowEnc := fun (ctx : SMT.Context) =>
      Except.ok (Term.app Op.bvult, TermType.prim .bool, ctx)
    -- UAddOverflow(x, y) = bvult(bvadd(x, y), x) — wrapping add < operand means overflow
    let uaddOverflowEnc := fun (_n : Nat) (ctx : SMT.Context) =>
      let app := fun (args : List Term) (_retTy : TermType) =>
        match args with
        | [x, y] =>
          let bvTy := x.typeOf
          let sum := Term.app Op.bvadd [x, y] bvTy
          Term.app Op.bvult [sum, x] .bool
        | _ => Term.app Op.and [] .bool
      Except.ok (app, TermType.prim .bool, ctx)
    -- UMulOverflow(x, y) = bvugt(zero_extend(N, x) * zero_extend(N, y), zero_extend(N, MAX))
    let umulOverflowEnc := fun (n : Nat) (ctx : SMT.Context) =>
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
      Except.ok (app, TermType.prim .bool, ctx)
    -- UNegOverflow(x) = x != 0
    let unegOverflowEnc := fun (n : Nat) (ctx : SMT.Context) =>
      let app := fun (args : List Term) (_retTy : TermType) =>
        match args with
        | [x] =>
          let zero := Term.prim (.bitvec (BitVec.zero n))
          Term.app Op.not [Term.app Op.eq [x, zero] .bool] .bool
        | _ => Term.app Op.and [] .bool
      Except.ok (app, TermType.prim .bool, ctx)
    match E.factory[fn.name]? with
    | none => .error f!"Cannot find function {fn} in Strata Core's Factory!"
    | some func =>
      match CoreOp.ofString func.name.name with
    | .bool .And     => .ok (.app Op.and,        .bool,   ctx)
    | .bool .Or      => .ok (.app Op.or,         .bool,   ctx)
    | .bool .Not     => .ok (.app Op.not,        .bool,   ctx)
    | .bool .Implies => .ok (.app Op.implies,    .bool,   ctx)
    | .bool .Equiv   => .ok (.app Op.eq,         .bool,   ctx)

    | .numeric ⟨.int, .Neg⟩      => .ok (.app Op.neg,        .int ,   ctx)
    | .numeric ⟨.int, .Add⟩      => .ok (.app Op.add,        .int ,   ctx)
    | .numeric ⟨.int, .Sub⟩      => .ok (.app Op.sub,        .int ,   ctx)
    | .numeric ⟨.int, .Mul⟩      => .ok (.app Op.mul,        .int ,   ctx)
    | .numeric ⟨.int, .Div⟩ | .numeric ⟨.int, .SafeDiv⟩ =>
      -- Safe to encode as normal SMT div/mod: preconditions have already been
      -- checked and generated well-formedness conditions in the environment.
      .ok (.app Op.div,        .int ,   ctx)
    | .numeric ⟨.int, .Mod⟩ | .numeric ⟨.int, .SafeMod⟩ =>
      .ok (.app Op.mod,        .int ,   ctx)
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
      .ok (divTApp, .int, ctx)
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
      .ok (modTApp, .int, ctx)
    | .numeric ⟨.int, .Lt⟩       => .ok (.app Op.lt,         .bool,   ctx)
    | .numeric ⟨.int, .Le⟩       => .ok (.app Op.le,         .bool,   ctx)
    | .numeric ⟨.int, .Gt⟩       => .ok (.app Op.gt,         .bool,   ctx)
    | .numeric ⟨.int, .Ge⟩       => .ok (.app Op.ge,         .bool,   ctx)

    | .numeric ⟨.real, .Neg⟩     => .ok (.app Op.neg,        .real,   ctx)
    | .numeric ⟨.real, .Add⟩     => .ok (.app Op.add,        .real,   ctx)
    | .numeric ⟨.real, .Sub⟩     => .ok (.app Op.sub,        .real,   ctx)
    | .numeric ⟨.real, .Mul⟩     => .ok (.app Op.mul,        .real,   ctx)
    | .numeric ⟨.real, .Div⟩     => .ok (.app Op.rdiv,       .real,   ctx)
    | .numeric ⟨.real, .Lt⟩      => .ok (.app Op.lt,         .bool,   ctx)
    | .numeric ⟨.real, .Le⟩      => .ok (.app Op.le,         .bool,   ctx)
    | .numeric ⟨.real, .Gt⟩      => .ok (.app Op.gt,         .bool,   ctx)
    | .numeric ⟨.real, .Ge⟩      => .ok (.app Op.ge,         .bool,   ctx)

    -- Bitvector operations: size-generic via CoreOp
    | .bv ⟨n, .Neg⟩  => .ok (.app Op.bvneg,      .bitvec n, ctx)
    | .bv ⟨n, .Add⟩  => .ok (.app Op.bvadd,      .bitvec n, ctx)
    | .bv ⟨n, .Sub⟩  => .ok (.app Op.bvsub,      .bitvec n, ctx)
    | .bv ⟨n, .Mul⟩  => .ok (.app Op.bvmul,      .bitvec n, ctx)
    | .bv ⟨n, .UDiv⟩ => .ok (.app Op.bvudiv,     .bitvec n, ctx)
    | .bv ⟨n, .UMod⟩ => .ok (.app Op.bvurem,     .bitvec n, ctx)
    | .bv ⟨n, .SDiv⟩ => .ok (.app Op.bvsdiv,     .bitvec n, ctx)
    | .bv ⟨n, .SMod⟩ => .ok (.app Op.bvsrem,     .bitvec n, ctx)
    | .bv ⟨n, .Not⟩  => .ok (.app Op.bvnot,      .bitvec n, ctx)
    | .bv ⟨n, .And⟩  => .ok (.app Op.bvand,      .bitvec n, ctx)
    | .bv ⟨n, .Or⟩   => .ok (.app Op.bvor,       .bitvec n, ctx)
    | .bv ⟨n, .Xor⟩  => .ok (.app Op.bvxor,      .bitvec n, ctx)
    | .bv ⟨n, .Shl⟩  => .ok (.app Op.bvshl,      .bitvec n, ctx)
    | .bv ⟨n, .UShr⟩ => .ok (.app Op.bvlshr,     .bitvec n, ctx)
    | .bv ⟨n, .SShr⟩ => .ok (.app Op.bvashr,     .bitvec n, ctx)
    | .bv ⟨_, .ULt⟩  => .ok (.app Op.bvult,      .bool,   ctx)
    | .bv ⟨_, .ULe⟩  => .ok (.app Op.bvule,      .bool,   ctx)
    | .bv ⟨_, .UGt⟩  => .ok (.app Op.bvugt,      .bool,   ctx)
    | .bv ⟨_, .UGe⟩  => .ok (.app Op.bvuge,      .bool,   ctx)
    | .bv ⟨_, .SLt⟩  => .ok (.app Op.bvslt,      .bool,   ctx)
    | .bv ⟨_, .SLe⟩  => .ok (.app Op.bvsle,      .bool,   ctx)
    | .bv ⟨_, .SGt⟩  => .ok (.app Op.bvsgt,      .bool,   ctx)
    | .bv ⟨_, .SGe⟩  => .ok (.app Op.bvsge,      .bool,   ctx)
    | .bv ⟨n, .Concat⟩ => .ok (.app Op.bvconcat, .bitvec (n * 2), ctx)

    | .str .Length   => .ok (.app Op.str_length,    .int,    ctx)
    | .str .Concat   => .ok (.app Op.str_concat,    .string, ctx)
    | .str .Substr   => .ok (.app Op.str_substr,    .string, ctx)
    | .str .ToRegEx  => .ok (.app Op.str_to_re,     .regex,  ctx)
    | .str .InRegEx  => .ok (.app Op.str_in_re,     .bool,   ctx)
    | .re .All       => .ok (.app Op.re_all,        .regex,  ctx)
    | .re .AllChar   => .ok (.app Op.re_allchar,    .regex,  ctx)
    | .re .Range     => .ok (.app Op.re_range,      .regex,  ctx)
    | .re .Concat    => .ok (.app Op.re_concat,     .regex,  ctx)
    | .re .Star      => .ok (.app Op.re_star,       .regex,  ctx)
    | .re .Plus      => .ok (.app Op.re_plus,       .regex,  ctx)
    | .re .Union     => .ok (.app Op.re_union,      .regex,  ctx)
    | .re .Inter     => .ok (.app Op.re_inter,      .regex,  ctx)
    | .re .Comp      => .ok (.app Op.re_comp,       .regex,  ctx)
    | .re .None      => .ok (.app Op.re_none,       .regex,  ctx)

    | .trigger .EmptyTriggers | .trigger .EmptyGroup =>
      .ok (.app Op.triggers, .trigger, ctx)
    | .trigger .AddTrigger | .trigger .AddGroup =>
      .ok (Factory.addTriggerList, .trigger, ctx)

    -- Safe BV operations: same encoding as unsafe (preconditions already checked)
    | .bv ⟨n, .SafeAdd⟩ => .ok (.app Op.bvadd, .bitvec n, ctx)
    | .bv ⟨n, .SafeSub⟩ => .ok (.app Op.bvsub, .bitvec n, ctx)
    | .bv ⟨n, .SafeMul⟩ => .ok (.app Op.bvmul, .bitvec n, ctx)
    | .bv ⟨n, .SafeNeg⟩ => .ok (.app Op.bvneg, .bitvec n, ctx)
    | .bv ⟨n, .SafeUAdd⟩ => .ok (.app Op.bvadd, .bitvec n, ctx)
    | .bv ⟨n, .SafeUSub⟩ => .ok (.app Op.bvsub, .bitvec n, ctx)
    | .bv ⟨n, .SafeUMul⟩ => .ok (.app Op.bvmul, .bitvec n, ctx)
    | .bv ⟨n, .SafeUNeg⟩ => .ok (.app Op.bvneg, .bitvec n, ctx)
    | .bv ⟨n, .SafeSDiv⟩ => .ok (.app Op.bvsdiv, .bitvec n, ctx)
    | .bv ⟨n, .SafeSMod⟩ => .ok (.app Op.bvsrem, .bitvec n, ctx)
    -- Signed overflow predicates
    | .bv ⟨_, .SAddOverflow⟩ => .ok (.app Op.bvsaddo, .bool, ctx)
    | .bv ⟨_, .SSubOverflow⟩ => .ok (.app Op.bvssubo, .bool, ctx)
    | .bv ⟨_, .SMulOverflow⟩ => .ok (.app Op.bvsmulo, .bool, ctx)
    | .bv ⟨_, .SNegOverflow⟩ => .ok (.app Op.bvnego, .bool, ctx)
    | .bv ⟨n, .SDivOverflow⟩ => sdivOverflowEnc n ctx
    -- Unsigned overflow predicates
    | .bv ⟨n, .UAddOverflow⟩ => uaddOverflowEnc n ctx
    | .bv ⟨_, .USubOverflow⟩ => usubOverflowEnc ctx
    | .bv ⟨n, .UMulOverflow⟩ => umulOverflowEnc n ctx
    | .bv ⟨n, .UNegOverflow⟩ => unegOverflowEnc n ctx

    | _ => do
      let fnname := func.name.name
      if (fnname == "select" || fnname == "update") && useArrayTheory then
        .ok (.app (if fnname == "select" then Op.select else Op.store), smt_outty, ctx)
      else
        let formals := func.inputs.keys
        let formalStrs := formals.map (toString ∘ format)
        let tys := LMonoTy.destructArrow fnty
        let intys := tys.take (tys.length - 1)
        let (smt_intys, ctx) ← LMonoTys.toSMTType E intys ctx useArrayTheory
        let bvs := formalStrs.zip smt_intys
        let argvars := bvs.map (fun a => TermVar.mk (toString $ format a.fst) a.snd)
        let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
        let (smt_outty, ctx) ← LMonoTy.toSMTType E outty ctx useArrayTheory
        let uf := ({id := (toString $ format fn), args := argvars, out := smt_outty})
        let (ctx, isNew) ←
          if func.isRecursive then
            .ok (ctx.addUF uf, !ctx.ufs.contains uf)
          else match func.body with
          | none => .ok (ctx.addUF uf, !ctx.ufs.contains uf)
          | some body =>
            -- Substitute the formals in the function body with appropriate
            -- `.bvar`s. Use substFvarsLifting to properly lift indices under binders.
            let bvars := (List.range formals.length).map (fun i => LExpr.bvar () i)
            let body := LExpr.substFvarsLifting body (formals.zip bvars)
            let (term, ctx) ← toSMTTerm E bvs body ctx
            .ok (ctx.addIF uf term,  !ctx.ifs.contains ({ uf := uf, body := term }))
        -- For recursive functions, generate per-constructor axioms
        let recAxioms ← if func.isRecursive && isNew then
            Lambda.genRecursiveAxioms func ctx.typeFactory E.exprEval ()
          else .ok []
        let allAxioms := func.axioms ++ recAxioms
        if isNew then
          -- To ensure termination, we add the axioms only for new functions
          -- Get the function's type patterns (input types + output type)
          let inputPatterns := func.inputs.values
          let outputPattern := func.output
          let allPatterns := inputPatterns ++ [outputPattern]

          -- Extract type instantiations by matching patterns against concrete types
          let type_instantiations: Map String LMonoTy := extractTypeInstantiations func.typeArgs allPatterns (intys ++ [outty])
          let smt_ty_inst ← type_instantiations.foldlM (fun acc_map (tyVar, monoTy) => do
            let (smtTy, _) ← LMonoTy.toSMTType E monoTy ctx useArrayTheory
            .ok (acc_map.insert tyVar smtTy)
          ) Map.empty
          -- Add all axioms for this function to the context, with types binding for the type variables in the expr
          -- Save the original tySubst to restore after processing axioms
          let savedSubst := ctx.tySubst
          let ctx ← allAxioms.foldlM (fun acc_ctx (ax: LExpr CoreLParams.mono) => do
            let current_axiom_ctx := acc_ctx.addSubst smt_ty_inst
              let (axiom_term, new_ctx) ← toSMTTerm E [] ax current_axiom_ctx
              .ok (new_ctx.addAxiom axiom_term)
          ) ctx
          let ctx := ctx.restoreSubst savedSubst
          .ok (.app (Op.uf uf), smt_outty, ctx)
        else
          .ok (.app (Op.uf uf), smt_outty, ctx)

end

def toSMTTerms (E : Env) (es : List (LExpr CoreLParams.mono)) (ctx : SMT.Context)
  (useArrayTheory : Bool := false) :
  Except Format ((List Term) × SMT.Context) := do
  let ctx := if ctx.typeFactory.isEmpty then ctx.withTypeFactory E.datatypes else ctx
  match es with
  | [] => .ok ([], ctx)
  | e :: erest =>
    let (et, ctx) ← toSMTTerm E [] e ctx useArrayTheory
    let (erestt, ctx) ← toSMTTerms E erest ctx useArrayTheory
    .ok ((et :: erestt), ctx)

/--
Encode a proof obligation into SMT terms: path conditions (P) and obligation (Q).
The obligation Q is returned without negation; see `encodeCore` in Verifier.lean
for the check-sat encoding that applies negation for validity checks.
-/
def ProofObligation.toSMTTerms (E : Env)
  (d : Imperative.ProofObligation Expression) (ctx : SMT.Context := SMT.Context.default)
  (useArrayTheory : Bool := false) :
  Except Format (List Term × Term × SMT.Context × Statistics) := do
  let assumptions := d.assumptions.flatten.map (fun a => a.snd)
  let (ctx, distinct_terms) ← E.distinct.foldlM (λ (ctx, tss) es =>
    do let (ts, ctx') ← Core.toSMTTerms E es ctx useArrayTheory; pure (ctx', ts :: tss)) (ctx, [])
  let distinct_assumptions := distinct_terms.map
    (λ ts => Term.app (.core .distinct) ts .bool)
  let (assumptions_terms, ctx) ← Core.toSMTTerms E assumptions ctx useArrayTheory
  let (obligation_term, ctx) ← Core.toSMTTerm E [] d.obligation ctx useArrayTheory
  let stats : Statistics := ({} : Statistics)
    |>.increment s!"{Evaluator.Stats.smtProofObligation_numAssumptions}"
        (distinct_assumptions.length + assumptions_terms.length)
  .ok (distinct_assumptions ++ assumptions_terms, obligation_term, ctx, stats)

---------------------------------------------------------------------

/-- Convert an expression of type LExpr to a String representation in SMT-Lib syntax, for testing.
    Outputs variable declarations followed by the assertion of the encoded term. -/
def toSMTCommandsWithAssert (e : LExpr CoreLParams.mono) (E : Env := Env.init) (ctx : SMT.Context := SMT.Context.default)
  (useArrayTheory : Bool := false)
  : IO String := do
  let smtctx := toSMTTerm E [] e ctx useArrayTheory
  match smtctx with
  | .error e => return e.pretty
  | .ok (smt, _) =>
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
