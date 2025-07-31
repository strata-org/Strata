/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Boogie
import Strata.DL.SMT.SMT
import Init.Data.String.Extra

---------------------------------------------------------------------

namespace Boogie
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
deriving Repr, DecidableEq, Inhabited

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

abbrev BoundVars := List (String × TermType)

---------------------------------------------------------------------

mutual
def LMonoTy.toSMTType (ty : LMonoTy) (ctx : SMT.Context) :
  Except Format (TermType × SMT.Context) := do
  match ty with
  | .bitvec n => .ok (.bitvec n, ctx)
  | .tcons "bool" [] => .ok (.bool, ctx)
  | .tcons "int"  [] => .ok (.int, ctx)
  | .tcons "real" [] => .ok (.real, ctx)
  | .tcons "string"  [] => .ok (.string, ctx)
  | .tcons id args =>
    let ctx := ctx.addSort { name := id, arity := args.length }
    let (args', ctx) ← LMonoTys.toSMTType args ctx
    .ok ((.constr id args'), ctx)
  | _ => .error f!"Unimplemented encoding for type {ty}"

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

mutual

partial def toSMTTerm (E : Env) (bvs : BoundVars) (e : LExpr BoogieIdent) (ctx : SMT.Context)
  : Except Format (Term × SMT.Context) := do
  match e with
  | .const "true" _ => .ok ((Term.bool true), ctx)
  | .const _ ty =>
    match ty with
    | none => .error f!"Cannot encode unannotated constant {e}"
    | some ty =>
        match ty with
        | .bool =>
          match e.denoteBool with
          | none =>
            .error f!"Unexpected boolean constant {e}"
          | some b => .ok ((Term.bool b), ctx)
        | .int =>
          match e.denoteInt with
          | none =>
            .error f!"Unexpected integer constant {e}"
          | some i => .ok ((Term.int i), ctx)
        | .real =>
          match e.denoteReal with
          | none =>
            .error f!"Unexpected real constant {e}"
          | some r => .ok ((Term.real r), ctx)
        | .bitvec n =>
          match e.denoteBitVec n with
          | none =>
            .error f!"Unexpected bv constant {e}"
          | some v => .ok ((Term.bitvec v), ctx)
        | .string =>
          match e.denoteString with
          | none => .error f!"Unexpected string constant {e}"
          | some s => .ok ((Term.string s), ctx)
        | _ =>
          .error f!"Unimplemented encoding for type {ty} in expression {e}"

  | .op fn fnty =>
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}."
    | some fnty =>
      -- 0-ary Operation.
      let (op, retty, ctx) ← toSMTOp E fn fnty ctx
      .ok ((Term.app op [] retty), ctx)

  | .bvar i =>
    if h: i < bvs.length
    then do
      let var := bvs[i]
      .ok ((TermVar.mk true var.fst var.snd), ctx)
    else .error f!"Bound variable index is out of bounds: {i}"

  | .fvar f ty =>
    match ty with
    | none => .error f!"Cannot encode unannotated free variable {e}"
    | some ty =>
      let (tty, ctx) ← LMonoTy.toSMTType ty ctx
      .ok ((TermVar.mk false (toString $ format f) tty), ctx)

  | .mdata _info e => do
    -- (FIXME) Add metadata as a comment in the SMT encoding.
    toSMTTerm E bvs e ctx

  | .abs ty e => .error f!"Cannot encode lambda abstraction {e}"

  | .quant _ .none _ => .error f!"Cannot encode untyped quantifier {e}"
  | .quant qk (.some ty) e =>
    let x := s!"$__bv{bvs.length}"
    let (ety, ctx) ← LMonoTy.toSMTType ty ctx
    let (et, ctx) ← toSMTTerm E ((x, ety) :: bvs) e ctx
    .ok ((Factory.quant (convertQuantifierKind qk) x ety et), ctx)

  | .eq e1 e2 =>
    let (e1t, ctx) ← toSMTTerm E bvs e1 ctx
    let (e2t, ctx) ← toSMTTerm E bvs e2 ctx
    .ok ((Factory.eq e1t e2t), ctx)

  | .ite c t f =>
    let (ct, ctx) ← toSMTTerm E bvs c ctx
    let (tt, ctx) ← toSMTTerm E bvs t ctx
    let (ft, ctx) ← toSMTTerm E bvs f ctx
    .ok ((Factory.ite ct tt ft), ctx)

  | .app _ _ => appToSMTTerm E bvs e [] ctx

partial def appToSMTTerm (E : Env) (bvs : BoundVars) (e : (LExpr BoogieIdent)) (acc : List Term) (ctx : SMT.Context) :
  Except Format (Term × SMT.Context) := do
  match e with
  | .app (.app fn e1) e2 => do
    let (e2t, ctx) ← toSMTTerm E bvs e2 ctx
    appToSMTTerm E bvs (.app fn e1) (e2t :: acc) ctx

  | .app (.op fn fnty) e1 => do
    match fnty with
    | none => .error f!"Cannot encode unannotated operation {fn}. \n\
                        Appears in expression: {e}"
    | some fnty =>
      let (op, retty, ctx) ← toSMTOp E fn fnty ctx
      let (e1t, ctx) ← toSMTTerm E bvs e1 ctx
      .ok ((Term.app op (e1t :: acc) retty), ctx)

  | .app _ _ =>
    .error f!"Cannot encode expression {e}"

  | _ => toSMTTerm E bvs e ctx

partial def toSMTOp (E : Env) (fn : BoogieIdent) (fnty : LMonoTy) (ctx : SMT.Context) :
  Except Format (Op × TermType × SMT.Context) :=
  open LTy.Syntax in
  match E.factory.getFactoryLFunc fn with
  | none => .error f!"Cannot find function {fn} in Boogie's Factory!"
  | some func =>
    match func.name.2 with
    | "Bool.And"     => .ok (Op.and,        .bool,   ctx)
    | "Bool.Or"      => .ok (Op.or,         .bool,   ctx)
    | "Bool.Not"     => .ok (Op.not,        .bool,   ctx)
    | "Bool.Implies" => .ok (Op.implies,    .bool,   ctx)
    | "Bool.Equiv"   => .ok (Op.eq,         .bool,   ctx)
    | "Int.Neg"      => .ok (Op.neg,        .int ,   ctx)
    | "Int.Add"      => .ok (Op.add,        .int ,   ctx)
    | "Int.Sub"      => .ok (Op.sub,        .int ,   ctx)
    | "Int.Mul"      => .ok (Op.mul,        .int ,   ctx)
    | "Int.Div"      => .ok (Op.div,        .int ,   ctx)
    | "Int.Mod"      => .ok (Op.mod,        .int ,   ctx)
    | "Int.Lt"       => .ok (Op.lt,         .bool,   ctx)
    | "Int.Le"       => .ok (Op.le,         .bool,   ctx)
    | "Int.Gt"       => .ok (Op.gt,         .bool,   ctx)
    | "Int.Ge"       => .ok (Op.ge,         .bool,   ctx)
    | "Real.Neg"     => .ok (Op.neg,        .real,   ctx)
    | "Real.Add"     => .ok (Op.add,        .real,   ctx)
    | "Real.Sub"     => .ok (Op.sub,        .real,   ctx)
    | "Real.Mul"     => .ok (Op.mul,        .real,   ctx)
    | "Real.Div"     => .ok (Op.div,        .real,   ctx)
    | "Real.Lt"      => .ok (Op.lt,         .bool,   ctx)
    | "Real.Le"      => .ok (Op.le,         .bool,   ctx)
    | "Real.Gt"      => .ok (Op.gt,         .bool,   ctx)
    | "Real.Ge"      => .ok (Op.ge,         .bool,   ctx)
    | "Bv1.Neg"     => .ok (Op.bvneg,      .bitvec 1, ctx)
    | "Bv1.Add"     => .ok (Op.bvadd,      .bitvec 1, ctx)
    | "Bv1.Sub"     => .ok (Op.bvsub,      .bitvec 1, ctx)
    | "Bv1.Mul"     => .ok (Op.bvmul,      .bitvec 1, ctx)
    | "Bv1.Lt"      => .ok (Op.bvult,      .bool,   ctx)
    | "Bv1.Le"      => .ok (Op.bvule,      .bool,   ctx)
    | "Bv8.Neg"     => .ok (Op.bvneg,      .bitvec 8, ctx)
    | "Bv8.Add"     => .ok (Op.bvadd,      .bitvec 8, ctx)
    | "Bv8.Sub"     => .ok (Op.bvsub,      .bitvec 8, ctx)
    | "Bv8.Mul"     => .ok (Op.bvmul,      .bitvec 8, ctx)
    | "Bv8.Lt"      => .ok (Op.bvult,      .bool,   ctx)
    | "Bv8.Le"      => .ok (Op.bvule,      .bool,   ctx)
    | "Bv16.Neg"     => .ok (Op.bvneg,      .bitvec 16, ctx)
    | "Bv16.Add"     => .ok (Op.bvadd,      .bitvec 16, ctx)
    | "Bv16.Sub"     => .ok (Op.bvsub,      .bitvec 16, ctx)
    | "Bv16.Mul"     => .ok (Op.bvmul,      .bitvec 16, ctx)
    | "Bv16.Lt"      => .ok (Op.bvult,      .bool,   ctx)
    | "Bv16.Le"      => .ok (Op.bvule,      .bool,   ctx)
    | "Bv32.Neg"     => .ok (Op.bvneg,      .bitvec 32, ctx)
    | "Bv32.Add"     => .ok (Op.bvadd,      .bitvec 32, ctx)
    | "Bv32.Sub"     => .ok (Op.bvsub,      .bitvec 32, ctx)
    | "Bv32.Mul"     => .ok (Op.bvmul,      .bitvec 32, ctx)
    | "Bv32.Lt"      => .ok (Op.bvult,      .bool,   ctx)
    | "Bv32.Le"      => .ok (Op.bvule,      .bool,   ctx)
    | "Bv64.Neg"     => .ok (Op.bvneg,      .bitvec 64, ctx)
    | "Bv64.Add"     => .ok (Op.bvadd,      .bitvec 64, ctx)
    | "Bv64.Sub"     => .ok (Op.bvsub,      .bitvec 64, ctx)
    | "Bv64.Mul"     => .ok (Op.bvmul,      .bitvec 64, ctx)
    | "Bv64.Lt"      => .ok (Op.bvult,      .bool,   ctx)
    | "Bv64.Le"      => .ok (Op.bvule,      .bool,   ctx)
    | "Str.Length"   => .ok (Op.str_length, .int,    ctx)
    | "Str.Concat"   => .ok (Op.str_concat, .string, ctx)
    | _ => do
      let formals := func.inputs.keys
      let formalStrs := formals.map (toString ∘ format)
      let tys := LMonoTy.destructArrow fnty
      let intys := tys.take (tys.length - 1)
      let (smt_intys, ctx) ← LMonoTys.toSMTType intys ctx
      let bvs := formalStrs.zip smt_intys
      let argvars := bvs.map (fun a => TermVar.mk true (toString $ format a.fst) a.snd)
      let outty := tys.getLast (by exact @LMonoTy.destructArrow_non_empty fnty)
      let (smt_outty, ctx) ← LMonoTy.toSMTType outty ctx
      let uf := ({id := (toString $ format fn), args := argvars, out := smt_outty})
      let ctx ←
        match func.body with
        | none => .ok (ctx.addUF uf)
        | some body =>
          -- Substitute the formals in the function body with appropriate
          -- `.bvar`s.
          let bvars := (List.range formals.length).map (fun i => LExpr.bvar i)
          let body := LExpr.substFvars body (formals.zip bvars)
          let (term, ctx) ← toSMTTerm E bvs body ctx
          .ok (ctx.addIF uf term)
      .ok (Op.uf uf, smt_outty, ctx)
end

def toSMTTerms (E : Env) (es : List (LExpr BoogieIdent)) (ctx : SMT.Context) :
  Except Format ((List Term) × SMT.Context) := do
  match es with
  | [] => .ok ([], ctx)
  | e :: erest =>
    let (et, ctx) ← toSMTTerm E [] e ctx
    let (erestt, ctx) ← toSMTTerms E erest ctx
    .ok ((et :: erestt), ctx)

def ProofObligation.toSMTTerms (E : Env)
  (d : Imperative.ProofObligation Expression) (ctx : SMT.Context := SMT.Context.default) :
  Except Format ((List Term) × SMT.Context) := do
  let assumptions := d.assumptions.flatten.map (fun a => a.snd)
  let (assumptions_terms, ctx) ← Boogie.toSMTTerms E assumptions ctx
  let (obligation_pos_term, ctx) ← Boogie.toSMTTerm E [] d.obligation ctx
  let obligation_term := Factory.not obligation_pos_term
  .ok ((assumptions_terms ++ [obligation_term]), ctx)

---------------------------------------------------------------------

/-- Convert an expression of type LExpr to a String representation in SMT-Lib syntax, for testing. -/
def toSMTTermString (e : (LExpr BoogieIdent)) (E : Env := Env.init) (ctx : SMT.Context := SMT.Context.default)
  : IO String := do
  let smtctx := toSMTTerm E [] e ctx
  match smtctx with
  | .error e => return e.pretty
  | .ok (smt, _) => Encoder.termToString smt

/-- info: "(define-fun t0 () Bool (forall (($__bv0 Int)) (exists (($__bv1 Int)) (= $__bv0 $__bv1))))\n" -/
#guard_msgs in
#eval toSMTTermString
  (.quant .all (.some .int)
   (.quant .exist (.some .int)
   (.eq (.bvar 1) (.bvar 0))))

/-- info: "; \"x\"\n(declare-const t0 Int)\n(define-fun t1 () Bool (exists (($__bv0 Int)) (= $__bv0 t0)))\n" -/
#guard_msgs in
#eval toSMTTermString
   (.quant .exist (.some .int)
   (.eq (.bvar 0) (.fvar "x" (.some .int))))

end Boogie
