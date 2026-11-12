/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.LowerGlobals

namespace Cortex.LowerDynamic

open Imperative Lambda

public section

def dynamicTy : String := "$Dynamic"
def boxTy : String := "$Box"
def toDynamicOp : String := "$toDynamic"
def fromDynamicOp : String := "$fromDynamic"

def toDynamic (t : LMonoTy) (e : Expr) : Expr :=
  .app () (.op () ⟨toDynamicOp, ()⟩ (some (.arrow t (tcon dynamicTy)))) e

def fromDynamic (t : LMonoTy) (e : Expr) : Expr :=
  .app () (.op () ⟨fromDynamicOp, ()⟩ (some (.arrow (tcon dynamicTy) t))) e

def boxCtor (t : LMonoTy) : String := s!"$Box${mangle t}"
def boxField (t : LMonoTy) : String := s!"$val${mangle t}"

def dynamicOp? : Expr → Option (Bool × LMonoTy)
  | .op _ o (some (.tcons "arrow" [a, b])) =>
    if o.name == toDynamicOp then some (true, a)
    else if o.name == fromDynamicOp then some (false, b)
    else none
  | _ => none

partial def boxedTys (e : Expr) : List LMonoTy :=
  match dynamicOp? e with
  | some (_, t) => [t]
  | none => match e with
    | .app _ a b | .eq _ a b => boxedTys a ++ boxedTys b
    | .ite _ c t f => boxedTys c ++ boxedTys t ++ boxedTys f
    | .abs _ _ _ b => boxedTys b
    | .quant _ _ _ _ tr b => boxedTys tr ++ boxedTys b
    | _ => []

def lowerExpr : Expr → Expr :=
  mapExpr fun e => (dynamicOp? e).map fun
    | (true, t) => mkOp (boxCtor t)
    | (false, t) => mkOp s!"$Box..{boxField t}!"

def programExprs (p : UnorderedProgram) : List Expr :=
  p.procedures.flatMap fun pr => match pr.body with
    | some b => b.cfg.blocks.flatMap fun (_, blk) =>
        blk.cmds.flatMap LowerGlobals.cmdExprs ++ LowerGlobals.transferExprs blk.transfer
    | none => []

def mkDatatype (name : String) (ctors : List (LConstr Unit)) (dflt : String) : LDatatype Unit :=
  let cs := if ctors.isEmpty then [{ name := ⟨dflt, ()⟩, args := [] }] else ctors
  have h : cs.length != 0 := by simp only [cs]; split <;> simp_all
  { name, typeArgs := [], constrs := cs, constrs_ne := h }

def run (p : UnorderedProgram) : Except String UnorderedProgram :=
  let tys := (programExprs p).flatMap boxedTys |>.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []
  let boxDt := mkDatatype boxTy (tys.map fun t => { name := ⟨boxCtor t, ()⟩, args := [(⟨boxField t, ()⟩, t)] }) "$NoBox"
  let q := p.mapProcedures fun pr => { pr with body := pr.body.map (mapBody (fun c => [mapCmdExprs lowerExpr id c]) lowerExpr) }
  let q := q.mapTys fun n => if n == dynamicTy then some (tcon boxTy) else none
  let (before, after) := q.datatypes.span (·.name != "$Heap")
  .ok { q with datatypes := before ++ boxDt :: after }

def pass : Pass := Pass.onUnordered "LowerDynamic" run

end

end Cortex.LowerDynamic
