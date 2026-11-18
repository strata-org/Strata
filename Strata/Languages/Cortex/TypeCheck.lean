/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module
public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.LExprT

namespace Cortex.TypeCheck

open Lambda
open Imperative (Cmd)

public section

abbrev Ctx := LContext Core.CoreLParams
abbrev Env := TEnv Unit
abbrev Gamma := List (Core.Expression.Ident × LMonoTy)

partial def eraseMono (prog : UnorderedProgram) : LMonoTy → LMonoTy
  | .tcons "Array" [_] => .tcons "$Composite" []
  | .tcons n [] =>
    if n.startsWith "$Any" || (prog.findComposite? n).isSome then .tcons "$Composite" []
    else match prog.constrained.find? (·.name == n) with
      | some c =>
        match LTy.toMonoType? (c.base : LTy) with
        | some b => eraseMono prog b
        | none => .tcons n []
      | none => .tcons n []
  | .tcons n args => .tcons n (args.map (eraseMono prog))
  | t => t

def eraseTy (prog : UnorderedProgram) (t : Core.Expression.Ty) : Except String LMonoTy :=
  match LTy.toMonoType? (t : LTy) with
  | some m => .ok (eraseMono prog m)
  | none => .error s!"polymorphic type {Std.format (t : LTy)} in Cortex"

def context (prog : UnorderedProgram) : Except String Ctx := do
  let C : Ctx := { LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }
  let C ← prog.opaqueTypes.foldlM (init := C) fun C tc =>
    (C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs }
      (Strata.Message.fromString s!"type {tc.name} is already known")).mapError (·.message)
  let C ← prog.composites.foldlM (init := C) fun C c =>
    if C.knownTypes.containsName c.name then pure C else
    (C.addKnownTypeWithError { name := c.name, metadata := 0 }
      (Strata.Message.fromString s!"type {c.name} is already known")).mapError (·.message)
  let C ← prog.datatypes.foldlM (init := C) fun C d => (C.addMutualBlock [d]).mapError (·.message)
  return prog.functions.foldl (init := C) fun C f => C.addFactoryFunction f

def bind (Γ : Gamma) (x : Core.Expression.Ident) (t : LMonoTy) : Except String Gamma :=
  match Γ.lookup x with
  | some t' => if t' == t then .ok Γ else
      .error s!"variable {x.name} is declared with the types {Std.format t'} and {Std.format t}"
  | none => .ok ((x, t) :: Γ)

def eraseExpr (prog : UnorderedProgram) : Expr → Expr :=
  mapExprMonoTys (eraseMono prog)

def annotate (prog : UnorderedProgram) (C : Ctx) (Γ : Gamma) (e : Expr) (expected : Option LMonoTy) :
    Except String Expr := do
  let e := eraseExpr prog e
  let env : Env := (TEnv.default.pushEmptyContext).addInNewestContext (T := Core.CoreLParams)
    (Strata.Util.HMap.ofList (Γ.map fun (x, t) => ((x : Core.CoreLParams.Identifier), LTy.forAll [] t)))
  let (et, env) ← (LExpr.resolve C env e).mapError fun f => s!"{f}"
  let S ← match expected with
    | some t => (Constraints.unify [(et.toLMonoTy, t)] env.stateSubstInfo).mapError fun f =>
        s!"expression {Std.format e} has type {Std.format et.toLMonoTy}, expected {Std.format t}: {Std.format f}"
    | none => pure env.stateSubstInfo
  return (LExpr.applySubstT et S.subst).unresolved

def varTy (Γ : Gamma) (x : Core.Expression.Ident) : Option LMonoTy := Γ.lookup x

def boolTy : LMonoTy := .bool

def calleeInputs (prog : UnorderedProgram) (n : ProcName) : Except String (Option (List LMonoTy)) :=
  match prog.findProcedure? n with
  | some p => do return some (← p.inputs.mapM fun (_, t) => eraseTy prog t)
  | none => return none

def annotateArgs (prog : UnorderedProgram) (C : Ctx) (Γ : Gamma) (tys : Option (List LMonoTy))
    (args : List Expr) : Except String (List Expr) :=
  match tys with
  | some ts =>
    if ts.length == args.length then (args.zip ts).mapM fun (a, t) => annotate prog C Γ a (some t)
    else args.mapM fun a => annotate prog C Γ a none
  | none => args.mapM fun a => annotate prog C Γ a none

def checkBaseCmd (prog : UnorderedProgram) (C : Ctx) (Γ : Gamma) :
    Cmd Core.Expression → Except String (Cmd Core.Expression)
  | .init x ty (.det e) md => do return .init x ty (.det (← annotate prog C Γ e (some (← eraseTy prog ty)))) md
  | .init x ty .nondet md => return .init x ty .nondet md
  | .set x (.det e) md => do return .set x (.det (← annotate prog C Γ e (varTy Γ x))) md
  | .set x .nondet md => return .set x .nondet md
  | .assert l e md => do return .assert l (← annotate prog C Γ e (some boolTy)) md
  | .assume l e md => do return .assume l (← annotate prog C Γ e (some boolTy)) md
  | .cover l e md => do return .cover l (← annotate prog C Γ e (some boolTy)) md

def checkCmd (prog : UnorderedProgram) (C : Ctx) (Γ : Gamma) : IRCmd → Except String IRCmd
  | .cmd c => do return .cmd (← checkBaseCmd prog C Γ c)
  | .cast x t e mode md => do return .cast x t (← annotate prog C Γ e (varTy Γ x)) mode md
  | .new x t md => return .new x t md
  | .readField x o f md => do return .readField x (← annotate prog C Γ o (some .int)) f md
  | .writeField o f v md => do
    let fty ← match prog.findField? f with
      | some d => pure (some (← eraseTy prog d.ty))
      | none => pure none
    return .writeField (← annotate prog C Γ o (some .int)) f (← annotate prog C Γ v fty) md
  | .instanceOf x o t md => do return .instanceOf x (← annotate prog C Γ o (some .int)) t md
  | .newArray x t len md => do return .newArray x t (← annotate prog C Γ len (some .int)) md
  | .readElem x a i ty md => do
    return .readElem x (← annotate prog C Γ a (some .int)) (← annotate prog C Γ i (some .int)) ty md
  | .writeElem a i v ty md => do
    return .writeElem (← annotate prog C Γ a (some .int)) (← annotate prog C Γ i (some .int))
      (← annotate prog C Γ v (some (← eraseTy prog ty))) ty md
  | .arrayLength x a md => do return .arrayLength x (← annotate prog C Γ a (some .int)) md
  | .instanceOfComponent x o a md => do
    return .instanceOfComponent x (← annotate prog C Γ o (some .int)) (← annotate prog C Γ a (some .int)) md
  | .call lhs n args md => do
    return .call lhs n (← annotateArgs prog C Γ (← calleeInputs prog n) args) md
  | .virtualCall lhs owner meth args md => do
    return .virtualCall lhs owner meth (← annotateArgs prog C Γ (← calleeInputs prog (implName owner meth)) args) md
  | .throw e md => do return .throw (← annotate prog C Γ e (some .int)) md

def checkTransfer (prog : UnorderedProgram) (C : Ctx) (Γ : Gamma) :
    Imperative.DetTransferCmd Label Core.Expression → Except String (Imperative.DetTransferCmd Label Core.Expression)
  | .condGoto e lt lf md => do return .condGoto (← annotate prog C Γ e (some boolTy)) lt lf md
  | .finish md => return .finish md

def frameTys (prog : UnorderedProgram) (p : Procedure) : Except String Gamma := do
  let Γ ← (p.inputs ++ p.outputs ++ prog.globals).foldlM (init := []) fun Γ (x, t) => do
    bind Γ x (← eraseTy prog t)
  match p.body with
  | none => return Γ
  | some b =>
    let Γ ← b.cfg.blocks.foldlM (init := Γ) fun Γ (_, blk) =>
      blk.cmds.foldlM (init := Γ) fun Γ c => match c with
        | .cmd (.init x ty _ _) => do bind Γ x (← eraseTy prog ty)
        | _ => pure Γ
    b.handlers.foldlM (init := Γ) fun Γ h => bind Γ h.binder .int

def checkProcedure (prog : UnorderedProgram) (C : Ctx) (p : Procedure) : Except String Procedure := do
  let Γ ← frameTys prog p
  let requires ← p.requires.mapM fun pre => do
    return { pre with cond := ← annotate prog C Γ pre.cond (some boolTy) }
  let body ← match p.body with
    | none => pure none
    | some b => do
      let blocks ← b.cfg.blocks.mapM fun (l, blk) => do
        let cmds ← blk.cmds.mapM (checkCmd prog C Γ)
        let transfer ← checkTransfer prog C Γ blk.transfer
        return (l, { cmds, transfer : LBlock })
      pure (some { b with cfg := { b.cfg with blocks } })
  return { p with requires, body }

def checkConstrained (prog : UnorderedProgram) (C : Ctx) (c : ConstrainedDecl) : Except String ConstrainedDecl := do
  let base ← eraseTy prog c.base
  let Γ := [(c.binder, base)]
  let constraint ← annotate prog C Γ c.constraint (some boolTy)
  let witness ← c.witness.mapM fun w => annotate prog C [] w (some base)
  return { c with constraint, witness }

def run (prog : UnorderedProgram) : Except String UnorderedProgram := do
  let C ← context prog
  let Γg ← prog.globals.foldlM (init := []) fun Γ (x, t) => do bind Γ x (← eraseTy prog t)
  let globalInit ← prog.globalInit.mapM (checkBaseCmd prog C Γg)
  let constrained ← prog.constrained.mapM (checkConstrained prog C)
  let functions ← prog.functions.mapM fun f => do
    let Γ := f.inputs.map fun (x, t) => ((⟨x.name, ()⟩ : Core.Expression.Ident), eraseMono prog t)
    let body ← f.body.mapM fun b => (annotate prog C Γ b (some (eraseMono prog f.output))).mapError
      fun e => s!"function {f.name.name}: {e}"
    return { f with body }
  let procedures ← prog.procedures.mapM fun p =>
    (checkProcedure prog C p).mapError fun e => s!"procedure {p.name}: {e}"
  return { prog with globalInit, constrained, functions, procedures }

end

end Cortex.TypeCheck
