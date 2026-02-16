/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Core
import Strata.DL.SMT.SMT
import Init.Data.String.Extra
import Strata.DDM.Util.DecimalRat

---------------------------------------------------------------------

namespace Core
open Std (ToFormat Format format)
open Lambda Strata.SMT

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
    let (c, i, s) := d.genFunctionMaps
    let m := Map.union ctx.datatypeFuns (c.fmap (fun (_, x) => (.constructor, x)))
    let m := Map.union m (i.fmap (fun (_, x) => (.tester, x)))
    let m := Map.union m (s.fmap (fun (_, x) => (.selector, x)))
    { ctx with seenDatatypes := ctx.seenDatatypes.insert d.name, datatypeFuns := m }

def SMT.Context.withTypeFactory (ctx : SMT.Context) (tf : @Lambda.TypeFactory CoreLParams.IDMeta) : SMT.Context :=
  { ctx with typeFactory := tf }

/--
Helper function to convert LMonoTy to SMT string representation.
For now, handles only monomorphic types and type variables without substitution.
-/
private def lMonoTyToSMTString (ty : LMonoTy) : String :=
  match ty with
  | .bitvec n => s!"(_ BitVec {n})"
  | .tcons "bool" [] => "Bool"
  | .tcons "int" [] => "Int"
  | .tcons "real" [] => "Real"
  | .tcons "string" [] => "String"
  | .tcons "regex" [] => "RegLan"
  | .tcons name args =>
    if args.isEmpty then name
    else s!"({name} {String.intercalate " " (args.map lMonoTyToSMTString)})"
  | .ftvar tv => tv

/-- Convert a datatype's constructors to SMT format. -/
private def datatypeConstructorsToSMT (d : LDatatype CoreLParams.IDMeta) : List String :=
  d.constrs.map fun c =>
    let fieldPairs := c.args.map fun (name, fieldTy) =>
              (d.name ++ ".." ++ name.name, lMonoTyToSMTString fieldTy)
    let fieldStrs := fieldPairs.map fun (name, ty) => s!"({name} {ty})"
    let fieldsStr := String.intercalate " " fieldStrs
    if c.args.isEmpty then s!"({c.name.name})"
    else s!"({c.name.name} {fieldsStr})"

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

abbrev BoundVars := List (String × TermType)

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


/-
Add a type to the context. Sorts are easy, but datatypes are tricky:
we must also ensure we add the types of all arguments in the constructors
to the context, recursively. This is very tricky to prove terminating, so
we leave as `partial` for now.
-/
partial def SMT.Context.addType (E: Env) (id: String) (args: List LMonoTy) (ctx: SMT.Context) :
  SMT.Context :=
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
def LMonoTy.toSMTType (E: Env) (ty : LMonoTy) (ctx : SMT.Context) :
  Except Format (TermType × SMT.Context) := do
  match ty with
  | .bitvec n => .ok (.bitvec n, ctx)
  | .tcons "bool" [] => .ok (.bool, ctx)
  | .tcons "int"  [] => .ok (.int, ctx)
  | .tcons "real" [] => .ok (.real, ctx)
  | .tcons "string"  [] => .ok (.string, ctx)
  | .tcons "regex" [] => .ok (.regex, ctx)
  | .tcons id args =>
    let ctx := SMT.Context.addType E id args ctx
    let (args', ctx) ← LMonoTys.toSMTType E args ctx
    .ok ((.constr id args'), ctx)
  | .ftvar tyv => match ctx.tySubst.find? tyv with
                    | .some termTy =>
                      .ok (termTy, ctx)
                    | _ => .error f!"Unimplemented encoding for type var {tyv}"

def LMonoTys.toSMTType (E: Env) (args : LMonoTys) (ctx : SMT.Context) :
    Except Format ((List TermType) × SMT.Context) := do
  match args with
  | [] => .ok ([], ctx)
  | t :: trest =>
    let (t', ctx) ← LMonoTy.toSMTType E t ctx
    let (trest', ctx) ← LMonoTys.toSMTType E trest ctx
    .ok ((t' :: trest'), ctx)
end

def convertQuantifierKind : Lambda.QuantifierKind -> Strata.SMT.QuantifierKind
  | .all => .all
  | .exist => .exist

mutual

partial def toSMTTerm (E : Env) (bvs : BoundVars) (e : LExpr CoreLParams.mono) (ctx : SMT.Context)
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
      let (op, retty, ctx) ← toSMTOp E fn fnty ctx
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
      let (tty, ctx) ← LMonoTy.toSMTType E ty ctx
      let uf := { id := (toString $ format f), args := [], out := tty }
      .ok (.app (.uf uf) [] tty, ctx.addUF uf)

  | .abs _ ty e => .error f!"Cannot encode lambda abstraction {e}"

  | .quant _ _ .none _ _ => .error f!"Cannot encode untyped quantifier {e}"
  | .quant _ qk (.some ty) tr e =>
    let x := s!"$__bv{bvs.length}"
    let (ety, ctx) ← LMonoTy.toSMTType E ty ctx
    let (trt, ctx) ← appToSMTTerm E ((x, ety) :: bvs) tr [] ctx
    let (et, ctx) ← toSMTTerm E ((x, ety) :: bvs) e ctx
    .ok (Factory.quant (convertQuantifierKind qk) x ety trt et, ctx)
  | .eq _ e1 e2 =>
    let (e1t, ctx) ← toSMTTerm E bvs e1 ctx
    let (e2t, ctx) ← toSMTTerm E bvs e2 ctx
    .ok ((Factory.eq e1t e2t), ctx)

  | .ite _ c t f =>
    let (ct, ctx) ← toSMTTerm E bvs c ctx
    let (tt, ctx) ← toSMTTerm E bvs t ctx
    let (ft, ctx) ← toSMTTerm E bvs f ctx
    .ok ((Factory.ite ct tt ft), ctx)

  | .app _ _ _ =>
    appToSMTTerm E bvs e [] ctx

partial def appToSMTTerm (E : Env) (bvs : BoundVars) (e : LExpr CoreLParams.mono) (acc : List Term) (ctx : SMT.Context) :
  Except Format (Term × SMT.Context) := do
  match e with
  -- Special case for indexed SMT operations.
  | .app _ (.app _ (.app _ (.op _ "Re.Loop" _) x) n1) n2 =>
    let (xt, ctx) ← toSMTTerm E bvs x ctx
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
      let (e2t, ctx) ← toSMTTerm E bvs e2 ctx
      appToSMTTerm E bvs (.app m fn e1) (e2t :: acc) ctx

  | .app _ (.op _ fn fnty) e1 => do
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}. \n\
                        Appears in expression: {e}"
    | some fnty =>
      let (op, retty, ctx) ← toSMTOp E fn fnty ctx
      let (e1t, ctx) ← toSMTTerm E bvs e1 ctx
      .ok (op (e1t :: acc) retty, ctx)
  | .app _ (.fvar _ fn (.some (.arrow intty outty))) e1 => do
    let (smt_outty, ctx) ← LMonoTy.toSMTType E outty ctx
    let (smt_intty, ctx) ← LMonoTy.toSMTType E intty ctx
    let argvars := [TermVar.mk (toString $ format intty) smt_intty]
    let (e1t, ctx) ← toSMTTerm E bvs e1 ctx
    let uf := UF.mk (id := (toString $ format fn)) (args := argvars) (out := smt_outty)
    .ok (((Term.app (.uf uf) [e1t] smt_outty)), ctx)
  | .app _ _ _ =>
    .error f!"Cannot encode expression {e}"

  | _ => toSMTTerm E bvs e ctx

partial def toSMTOp (E : Env) (fn : CoreIdent) (fnty : LMonoTy) (ctx : SMT.Context) :
  Except Format ((List Term → TermType → Term) × TermType × SMT.Context) :=
  open LTy.Syntax in do
  -- Encode the type to ensure any datatypes are registered in the context
  let tys := LMonoTy.destructArrow fnty
  let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
  let intys := tys.take (tys.length - 1)
  -- Need to encode arg types also (e.g. for testers)
  let ctx := match LMonoTys.toSMTType E intys ctx with
    | .ok (_, ctx') => ctx'
    | .error _ => ctx
  let (smt_outty, ctx) ← LMonoTy.toSMTType E outty ctx

  match ctx.datatypeFuns.find? fn.name with
  | some (kind, c) =>
    let adtApp := fun (args : List Term) (retty : TermType) =>
        /-
        Note: testers use constructor, translated in `Op.mkName` to is-foo
        Selectors use full function name (Datatype..fieldName) for uniqueness
        -/
        let name := match kind with
          | .selector => fn.name
          | _ => c.name.name
        Term.app (.datatype_op kind name) args retty
    .ok (adtApp, smt_outty, ctx)
  | none =>
    -- Not a constructor, tester, or destructor
    match E.factory.getFactoryLFunc fn.name with
    | none => .error f!"Cannot find function {fn} in Strata Core's Factory!"
    | some func =>
      match func.name.name with
    | "Bool.And"     => .ok (.app Op.and,        .bool,   ctx)
    | "Bool.Or"      => .ok (.app Op.or,         .bool,   ctx)
    | "Bool.Not"     => .ok (.app Op.not,        .bool,   ctx)
    | "Bool.Implies" => .ok (.app Op.implies,    .bool,   ctx)
    | "Bool.Equiv"   => .ok (.app Op.eq,         .bool,   ctx)

    | "Int.Neg"      => .ok (.app Op.neg,        .int ,   ctx)
    | "Int.Add"      => .ok (.app Op.add,        .int ,   ctx)
    | "Int.Sub"      => .ok (.app Op.sub,        .int ,   ctx)
    | "Int.Mul"      => .ok (.app Op.mul,        .int ,   ctx)
    | "Int.Div"      => .ok (.app Op.div,        .int ,   ctx)
    | "Int.Mod"      => .ok (.app Op.mod,        .int ,   ctx)
    -- Truncating division: tdiv(a,b) = let q = ediv(abs(a), abs(b)) in ite(a*b >= 0, q, -q)
    | "Int.DivT"     =>
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
    | "Int.ModT"     =>
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
    | "Int.Lt"       => .ok (.app Op.lt,         .bool,   ctx)
    | "Int.Le"       => .ok (.app Op.le,         .bool,   ctx)
    | "Int.Gt"       => .ok (.app Op.gt,         .bool,   ctx)
    | "Int.Ge"       => .ok (.app Op.ge,         .bool,   ctx)

    | "Real.Neg"     => .ok (.app Op.neg,        .real,   ctx)
    | "Real.Add"     => .ok (.app Op.add,        .real,   ctx)
    | "Real.Sub"     => .ok (.app Op.sub,        .real,   ctx)
    | "Real.Mul"     => .ok (.app Op.mul,        .real,   ctx)
    | "Real.Div"     => .ok (.app Op.div,        .real,   ctx)
    | "Real.Lt"      => .ok (.app Op.lt,         .bool,   ctx)
    | "Real.Le"      => .ok (.app Op.le,         .bool,   ctx)
    | "Real.Gt"      => .ok (.app Op.gt,         .bool,   ctx)
    | "Real.Ge"      => .ok (.app Op.ge,         .bool,   ctx)

    | "Bv1.Neg"     => .ok (.app Op.bvneg,      .bitvec 1, ctx)
    | "Bv1.Add"     => .ok (.app Op.bvadd,      .bitvec 1, ctx)
    | "Bv1.Sub"     => .ok (.app Op.bvsub,      .bitvec 1, ctx)
    | "Bv1.Mul"     => .ok (.app Op.bvmul,      .bitvec 1, ctx)
    | "Bv1.UDiv"    => .ok (.app Op.bvudiv,     .bitvec 1, ctx)
    | "Bv1.UMod"    => .ok (.app Op.bvurem,     .bitvec 1, ctx)
    | "Bv1.SDiv"    => .ok (.app Op.bvsdiv,     .bitvec 1, ctx)
    | "Bv1.SMod"    => .ok (.app Op.bvsrem,     .bitvec 1, ctx)
    | "Bv1.Not"     => .ok (.app Op.bvnot,      .bitvec 1, ctx)
    | "Bv1.And"     => .ok (.app Op.bvand,      .bitvec 1, ctx)
    | "Bv1.Or"      => .ok (.app Op.bvor,       .bitvec 1, ctx)
    | "Bv1.Xor"     => .ok (.app Op.bvxor,      .bitvec 1, ctx)
    | "Bv1.Shl"     => .ok (.app Op.bvshl,      .bitvec 1, ctx)
    | "Bv1.UShr"    => .ok (.app Op.bvlshr,     .bitvec 1, ctx)
    | "Bv1.SShr"    => .ok (.app Op.bvashr,     .bitvec 1, ctx)
    | "Bv1.ULt"     => .ok (.app Op.bvult,      .bool,   ctx)
    | "Bv1.ULe"     => .ok (.app Op.bvule,      .bool,   ctx)
    | "Bv1.UGt"     => .ok (.app Op.bvugt,      .bool,   ctx)
    | "Bv1.UGe"     => .ok (.app Op.bvuge,      .bool,   ctx)
    | "Bv1.SLt"     => .ok (.app Op.bvslt,      .bool,   ctx)
    | "Bv1.SLe"     => .ok (.app Op.bvsle,      .bool,   ctx)
    | "Bv1.SGt"     => .ok (.app Op.bvsgt,      .bool,   ctx)
    | "Bv1.SGe"     => .ok (.app Op.bvsge,      .bool,   ctx)

    | "Bv8.Neg"     => .ok (.app Op.bvneg,      .bitvec 8, ctx)
    | "Bv8.Add"     => .ok (.app Op.bvadd,      .bitvec 8, ctx)
    | "Bv8.Sub"     => .ok (.app Op.bvsub,      .bitvec 8, ctx)
    | "Bv8.Mul"     => .ok (.app Op.bvmul,      .bitvec 8, ctx)
    | "Bv8.UDiv"    => .ok (.app Op.bvudiv,     .bitvec 8, ctx)
    | "Bv8.SDiv"    => .ok (.app Op.bvsdiv,     .bitvec 8, ctx)
    | "Bv8.UMod"    => .ok (.app Op.bvurem,     .bitvec 8, ctx)
    | "Bv8.SMod"    => .ok (.app Op.bvsrem,     .bitvec 8, ctx)
    | "Bv8.Not"     => .ok (.app Op.bvnot,      .bitvec 8, ctx)
    | "Bv8.And"     => .ok (.app Op.bvand,      .bitvec 8, ctx)
    | "Bv8.Or"      => .ok (.app Op.bvor,       .bitvec 8, ctx)
    | "Bv8.Xor"     => .ok (.app Op.bvxor,      .bitvec 8, ctx)
    | "Bv8.Shl"     => .ok (.app Op.bvshl,      .bitvec 8, ctx)
    | "Bv8.UShr"    => .ok (.app Op.bvlshr,     .bitvec 8, ctx)
    | "Bv8.SShr"    => .ok (.app Op.bvashr,     .bitvec 8, ctx)
    | "Bv8.ULt"     => .ok (.app Op.bvult,      .bool,   ctx)
    | "Bv8.ULe"     => .ok (.app Op.bvule,      .bool,   ctx)
    | "Bv8.UGt"     => .ok (.app Op.bvugt,      .bool,   ctx)
    | "Bv8.UGe"     => .ok (.app Op.bvuge,      .bool,   ctx)
    | "Bv8.SLt"     => .ok (.app Op.bvslt,      .bool,   ctx)
    | "Bv8.SLe"     => .ok (.app Op.bvsle,      .bool,   ctx)
    | "Bv8.SGt"     => .ok (.app Op.bvsgt,      .bool,   ctx)
    | "Bv8.SGe"     => .ok (.app Op.bvsge,      .bool,   ctx)

    | "Bv16.Neg"     => .ok (.app Op.bvneg,      .bitvec 16, ctx)
    | "Bv16.Add"     => .ok (.app Op.bvadd,      .bitvec 16, ctx)
    | "Bv16.Sub"     => .ok (.app Op.bvsub,      .bitvec 16, ctx)
    | "Bv16.Mul"     => .ok (.app Op.bvmul,      .bitvec 16, ctx)
    | "Bv16.UDiv"    => .ok (.app Op.bvudiv,     .bitvec 16, ctx)
    | "Bv16.UMod"    => .ok (.app Op.bvurem,     .bitvec 16, ctx)
    | "Bv16.SDiv"    => .ok (.app Op.bvsdiv,     .bitvec 16, ctx)
    | "Bv16.SMod"    => .ok (.app Op.bvsrem,     .bitvec 16, ctx)
    | "Bv16.Not"     => .ok (.app Op.bvnot,      .bitvec 16, ctx)
    | "Bv16.And"     => .ok (.app Op.bvand,      .bitvec 16, ctx)
    | "Bv16.Or"      => .ok (.app Op.bvor,       .bitvec 16, ctx)
    | "Bv16.Xor"     => .ok (.app Op.bvxor,      .bitvec 16, ctx)
    | "Bv16.Shl"     => .ok (.app Op.bvshl,      .bitvec 16, ctx)
    | "Bv16.UShr"    => .ok (.app Op.bvlshr,     .bitvec 16, ctx)
    | "Bv16.SShr"    => .ok (.app Op.bvashr,     .bitvec 16, ctx)
    | "Bv16.ULt"     => .ok (.app Op.bvult,      .bool,   ctx)
    | "Bv16.ULe"     => .ok (.app Op.bvule,      .bool,   ctx)
    | "Bv16.UGt"     => .ok (.app Op.bvugt,      .bool,   ctx)
    | "Bv16.UGe"     => .ok (.app Op.bvuge,      .bool,   ctx)
    | "Bv16.SLt"     => .ok (.app Op.bvslt,      .bool,   ctx)
    | "Bv16.SLe"     => .ok (.app Op.bvsle,      .bool,   ctx)
    | "Bv16.SGt"     => .ok (.app Op.bvsgt,      .bool,   ctx)
    | "Bv16.SGe"     => .ok (.app Op.bvsge,      .bool,   ctx)

    | "Bv32.Neg"     => .ok (.app Op.bvneg,      .bitvec 32, ctx)
    | "Bv32.Add"     => .ok (.app Op.bvadd,      .bitvec 32, ctx)
    | "Bv32.Sub"     => .ok (.app Op.bvsub,      .bitvec 32, ctx)
    | "Bv32.Mul"     => .ok (.app Op.bvmul,      .bitvec 32, ctx)
    | "Bv32.UDiv"    => .ok (.app Op.bvudiv,     .bitvec 32, ctx)
    | "Bv32.UMod"    => .ok (.app Op.bvurem,     .bitvec 32, ctx)
    | "Bv32.SDiv"    => .ok (.app Op.bvsdiv,     .bitvec 32, ctx)
    | "Bv32.SMod"    => .ok (.app Op.bvsrem,     .bitvec 32, ctx)
    | "Bv32.Not"     => .ok (.app Op.bvnot,      .bitvec 32, ctx)
    | "Bv32.And"     => .ok (.app Op.bvand,      .bitvec 32, ctx)
    | "Bv32.Or"      => .ok (.app Op.bvor,       .bitvec 32, ctx)
    | "Bv32.Xor"     => .ok (.app Op.bvxor,      .bitvec 32, ctx)
    | "Bv32.Shl"     => .ok (.app Op.bvshl,      .bitvec 32, ctx)
    | "Bv32.UShr"    => .ok (.app Op.bvlshr,     .bitvec 32, ctx)
    | "Bv32.SShr"    => .ok (.app Op.bvashr,     .bitvec 32, ctx)
    | "Bv32.ULt"     => .ok (.app Op.bvult,      .bool,   ctx)
    | "Bv32.ULe"     => .ok (.app Op.bvule,      .bool,   ctx)
    | "Bv32.UGt"     => .ok (.app Op.bvugt,      .bool,   ctx)
    | "Bv32.UGe"     => .ok (.app Op.bvuge,      .bool,   ctx)
    | "Bv32.SLt"     => .ok (.app Op.bvslt,      .bool,   ctx)
    | "Bv32.SLe"     => .ok (.app Op.bvsle,      .bool,   ctx)
    | "Bv32.SGt"     => .ok (.app Op.bvsgt,      .bool,   ctx)
    | "Bv32.SGe"     => .ok (.app Op.bvsge,      .bool,   ctx)

    | "Bv64.Neg"     => .ok (.app Op.bvneg,      .bitvec 64, ctx)
    | "Bv64.Add"     => .ok (.app Op.bvadd,      .bitvec 64, ctx)
    | "Bv64.Sub"     => .ok (.app Op.bvsub,      .bitvec 64, ctx)
    | "Bv64.Mul"     => .ok (.app Op.bvmul,      .bitvec 64, ctx)
    | "Bv64.UDiv"    => .ok (.app Op.bvudiv,     .bitvec 64, ctx)
    | "Bv64.UMod"    => .ok (.app Op.bvurem,     .bitvec 64, ctx)
    | "Bv64.SDiv"    => .ok (.app Op.bvsdiv,     .bitvec 64, ctx)
    | "Bv64.SMod"    => .ok (.app Op.bvsrem,     .bitvec 64, ctx)
    | "Bv64.Not"     => .ok (.app Op.bvnot,      .bitvec 64, ctx)
    | "Bv64.And"     => .ok (.app Op.bvand,      .bitvec 64, ctx)
    | "Bv64.Or"      => .ok (.app Op.bvor,       .bitvec 64, ctx)
    | "Bv64.Xor"     => .ok (.app Op.bvxor,      .bitvec 64, ctx)
    | "Bv64.Shl"     => .ok (.app Op.bvshl,      .bitvec 64, ctx)
    | "Bv64.UShr"    => .ok (.app Op.bvlshr,     .bitvec 64, ctx)
    | "Bv64.SShr"    => .ok (.app Op.bvashr,     .bitvec 64, ctx)
    | "Bv64.ULt"     => .ok (.app Op.bvult,      .bool,   ctx)
    | "Bv64.ULe"     => .ok (.app Op.bvule,      .bool,   ctx)
    | "Bv64.UGt"     => .ok (.app Op.bvugt,      .bool,   ctx)
    | "Bv64.UGe"     => .ok (.app Op.bvuge,      .bool,   ctx)
    | "Bv64.SLt"     => .ok (.app Op.bvslt,      .bool,   ctx)
    | "Bv64.SLe"     => .ok (.app Op.bvsle,      .bool,   ctx)
    | "Bv64.SGt"     => .ok (.app Op.bvsgt,      .bool,   ctx)
    | "Bv64.SGe"     => .ok (.app Op.bvsge,      .bool,   ctx)

    | "Bv8.Concat"   => .ok (.app Op.bvconcat,   .bitvec 16, ctx)
    | "Bv16.Concat"  => .ok (.app Op.bvconcat,   .bitvec 32, ctx)
    | "Bv32.Concat"  => .ok (.app Op.bvconcat,   .bitvec 64, ctx)

    | "Str.Length"   => .ok (.app Op.str_length,    .int,    ctx)
    | "Str.Concat"   => .ok (.app Op.str_concat,    .string, ctx)
    | "Str.Substr"   => .ok (.app Op.str_substr,    .string, ctx)
    | "Str.ToRegEx"  => .ok (.app Op.str_to_re,     .regex,  ctx)
    | "Str.InRegEx"  => .ok (.app Op.str_in_re,     .bool,   ctx)
    | "Re.All"       => .ok (.app Op.re_all,        .regex,  ctx)
    | "Re.AllChar"   => .ok (.app Op.re_allchar,    .regex,  ctx)
    | "Re.Range"     => .ok (.app Op.re_range,      .regex,  ctx)
    | "Re.Concat"    => .ok (.app Op.re_concat,     .regex,  ctx)
    | "Re.Star"      => .ok (.app Op.re_star,       .regex,  ctx)
    | "Re.Plus"      => .ok (.app Op.re_plus,       .regex,  ctx)
    | "Re.Union"     => .ok (.app Op.re_union,      .regex,  ctx)
    | "Re.Inter"     => .ok (.app Op.re_inter,      .regex,  ctx)
    | "Re.Comp"      => .ok (.app Op.re_comp,       .regex,  ctx)
    | "Re.None"      => .ok (.app Op.re_none,       .regex,  ctx)

    | "Triggers.empty"          => .ok (.app Op.triggers, .trigger, ctx)
    | "TriggerGroup.empty"      => .ok (.app Op.triggers, .trigger, ctx)
    | "TriggerGroup.addTrigger" => .ok (Factory.addTriggerList, .trigger, ctx)
    | "Triggers.addGroup"       => .ok (Factory.addTriggerList, .trigger, ctx)
    | _ => do
      let formals := func.inputs.keys
      let formalStrs := formals.map (toString ∘ format)
      let tys := LMonoTy.destructArrow fnty
      let intys := tys.take (tys.length - 1)
      let (smt_intys, ctx) ← LMonoTys.toSMTType E intys ctx
      let bvs := formalStrs.zip smt_intys
      let argvars := bvs.map (fun a => TermVar.mk (toString $ format a.fst) a.snd)
      let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
      let (smt_outty, ctx) ← LMonoTy.toSMTType E outty ctx
      let uf := ({id := (toString $ format fn), args := argvars, out := smt_outty})
      let (ctx, isNew) ←
        match func.body with
        | none => .ok (ctx.addUF uf, !ctx.ufs.contains uf)
        | some body =>
          -- Substitute the formals in the function body with appropriate
          -- `.bvar`s.
          let bvars := (List.range formals.length).map (fun i => LExpr.bvar () i)
          let body := LExpr.substFvars body (formals.zip bvars)
          let (term, ctx) ← toSMTTerm E bvs body ctx
          .ok (ctx.addIF uf term,  !ctx.ifs.contains ({ uf := uf, body := term }))
      if isNew then
        -- To ensure termination, we add the axioms only for new functions
        -- Get the function's type patterns (input types + output type)
        let inputPatterns := func.inputs.values
        let outputPattern := func.output
        let allPatterns := inputPatterns ++ [outputPattern]

        -- Extract type instantiations by matching patterns against concrete types
        let type_instantiations: Map String LMonoTy := extractTypeInstantiations func.typeArgs allPatterns (intys ++ [outty])
        let smt_ty_inst ← type_instantiations.foldlM (fun acc_map (tyVar, monoTy) => do
          let (smtTy, _) ← LMonoTy.toSMTType E monoTy ctx
          .ok (acc_map.insert tyVar smtTy)
        ) Map.empty
        -- Add all axioms for this function to the context, with types binding for the type variables in the expr
        -- Save the original tySubst to restore after processing axioms
        let savedSubst := ctx.tySubst
        let ctx ← func.axioms.foldlM (fun acc_ctx (ax: LExpr CoreLParams.mono) => do
          let current_axiom_ctx := acc_ctx.addSubst smt_ty_inst
            let (axiom_term, new_ctx) ← toSMTTerm E [] ax current_axiom_ctx
            .ok (new_ctx.addAxiom axiom_term)
        ) ctx
        let ctx := ctx.restoreSubst savedSubst
        .ok (.app (Op.uf uf), smt_outty, ctx)
      else
        .ok (.app (Op.uf uf), smt_outty, ctx)
end

def toSMTTerms (E : Env) (es : List (LExpr CoreLParams.mono)) (ctx : SMT.Context) :
  Except Format ((List Term) × SMT.Context) := do
  let ctx := if ctx.typeFactory.isEmpty then ctx.withTypeFactory E.datatypes else ctx
  match es with
  | [] => .ok ([], ctx)
  | e :: erest =>
    let (et, ctx) ← toSMTTerm E [] e ctx
    let (erestt, ctx) ← toSMTTerms E erest ctx
    .ok ((et :: erestt), ctx)

/--
Encode a proof obligation -- which may be of type `assert` or `cover` -- into
SMTLIB.

Under conditions `P`, `assert(Q)` is encoded into SMTLib as follows:
```
(assert P)
(assert (not Q))
(check-sat)
```
If the result is `unsat`, then `P ∧ ¬Q` is unsatisfiable, which means `P => Q`
is valid. If the result is `sat`, then the assertion is violated.

Under conditions `P`, `cover(Q)` is encoded into SMTLib as follows:
```
(assert P)
(assert Q)
(check-sat)
```
If the result is `unsat`, then `P ∧ Q` is unsatisfiable, which means that the
cover is violated. If the result is `sat`, then the cover succeeds.
-/
def ProofObligation.toSMTTerms (E : Env)
  (d : Imperative.ProofObligation Expression) (ctx : SMT.Context := SMT.Context.default) :
  Except Format ((List Term) × SMT.Context) := do
  let assumptions := d.assumptions.flatten.map (fun a => a.snd)
  let (ctx, distinct_terms) ← E.distinct.foldlM (λ (ctx, tss) es =>
    do let (ts, ctx') ← Core.toSMTTerms E es ctx; pure (ctx', ts :: tss)) (ctx, [])
  let distinct_assumptions := distinct_terms.map
    (λ ts => Term.app (.core .distinct) ts .bool)
  let (assumptions_terms, ctx) ← Core.toSMTTerms E assumptions ctx
  let (obligation_pos_term, ctx) ← Core.toSMTTerm E [] d.obligation ctx
  let obligation_term :=
    if d.property == .cover then
      obligation_pos_term
    else
      Factory.not obligation_pos_term
  .ok ((distinct_assumptions ++ assumptions_terms ++ [obligation_term]), ctx)

---------------------------------------------------------------------

/-- Convert an expression of type LExpr to a String representation in SMT-Lib syntax, for testing. -/
def toSMTTermString (e : LExpr CoreLParams.mono) (E : Env := Env.init) (ctx : SMT.Context := SMT.Context.default)
  : IO String := do
  let smtctx := toSMTTerm E [] e ctx
  match smtctx with
  | .error e => return e.pretty
  | .ok (smt, _) => Encoder.termToString smt

end Core
