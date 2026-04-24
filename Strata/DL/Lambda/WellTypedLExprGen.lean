/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Plausible.Gen
public meta import Plausible.Arbitrary
public meta import Plausible.DeriveArbitrary
public meta import Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.TestGen
public meta import Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExprT

/-!
  Hand-crafted generator for well-typed LExpr terms.

  The generator is parameterized by all components of the `HasType` relation:
  - `T : LExprParams` — expression metadata and identifier metadata types
  - `C : LContext T` — known types, factory functions, datatypes
  - `Γ : TContext T.IDMeta` — typing context (free variable bindings, aliases)
  - `ty : LMonoTy` — target monotype (optional; randomly chosen if not given)

  The generator is *complete*: every LExpr constructor that `resolve` accepts
  can be produced (const incl. real/bitvec, fvar, bvar via abs/quant, app, ite,
  eq, abs via fvar+varClose, quant, op with 0/1/2-arg application).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Plausible
open Lambda

public meta section

namespace WTG

/-! ## Binder context -/

abbrev BCtx := List (Nat × LMonoTy)

private def shiftCtx (ctx : BCtx) : BCtx :=
  ctx.map fun (i, t) => (i + 1, t)

private def matchingBinders (ctx : BCtx) (ty : LMonoTy) : List Nat :=
  ctx.filterMap fun (i, t) => if t == ty then some i else none

/-! ## Precomputed info from parameters -/

structure OpInfo (IDMeta : Type) where
  name : Identifier IDMeta
  argTypes : List LMonoTy
  resultType : LMonoTy
deriving Inhabited

structure FVarInfo (IDMeta : Type) where
  ident : Identifier IDMeta
  monoTy : LMonoTy
deriving Inhabited

structure GenEnv (T : LExprParams) where
  ops : List (OpInfo T.IDMeta)
  fvars : List (FVarInfo T.IDMeta)
  knownBaseTypes : List LMonoTy
  ctx : LContext T

private def extractOps {T : LExprParams} (C : LContext T) : List (OpInfo T.IDMeta) :=
  C.functions.toArray.toList.filterMap fun f =>
    if f.typeArgs.isEmpty then
      some { name := f.name, argTypes := f.inputs.values, resultType := f.output }
    else none

private def opsForType {T : LExprParams} (ops : List (OpInfo T.IDMeta)) (ty : LMonoTy)
    : List (OpInfo T.IDMeta) :=
  ops.filter fun op => op.resultType == ty

private def opsWithFullType {T : LExprParams} (ops : List (OpInfo T.IDMeta)) (ty : LMonoTy)
    : List (OpInfo T.IDMeta) :=
  ops.filter fun op =>
    let fullTy := op.argTypes.foldr (fun arg acc => .tcons "arrow" [arg, acc]) op.resultType
    fullTy == ty

private def extractFVars {IDMeta : Type} [DecidableEq IDMeta]
    (Γ : TContext IDMeta) : List (FVarInfo IDMeta) :=
  Γ.types.foldl (init := []) fun acc scope =>
    acc ++ scope.filterMap fun (ident, ty) =>
      match ty with
      | .forAll [] mty => some { ident, monoTy := mty }
      | _ => none

private def extractBaseTypes {T : LExprParams} (C : LContext T) : List LMonoTy :=
  let names := ["bool", "int", "string", "real"]
  let bases := names.filterMap fun name =>
    if C.knownTypes.containsName name then some (.tcons name []) else none
  let bvs := if C.knownTypes.containsName "bitvec"
    then [.bitvec 1, .bitvec 8, .bitvec 16, .bitvec 32, .bitvec 64] else []
  bases ++ bvs

private def mkGenEnv {T : LExprParams} [DecidableEq T.IDMeta]
    (C : LContext T) (Γ : TContext T.IDMeta) : GenEnv T :=
  { ops := extractOps C, fvars := extractFVars Γ, knownBaseTypes := extractBaseTypes C, ctx := C }

private def fvarsForType {IDMeta} (fvars : List (FVarInfo IDMeta)) (ty : LMonoTy)
    : List (FVarInfo IDMeta) :=
  fvars.filter fun fv => fv.monoTy == ty

/-! ## Type generation -/

private def genBaseType (bases : List LMonoTy) : Gen LMonoTy :=
  match bases with
  | [] => pure .bool
  | _ => Gen.oneOfWithDefault (pure .bool) (bases.map pure)

private def genType (bases : List LMonoTy) : Nat → Gen LMonoTy
  | 0 => genBaseType bases
  | n + 1 => Gen.frequency (genBaseType bases) [
      (4, genBaseType bases),
      (1, do let d ← genType bases n; let c ← genType bases n
             pure (.tcons "arrow" [d, c]))]

/-! ## Leaf generators -/

variable {T : LExprParams} [Arbitrary T.Metadata] [Arbitrary T.IDMeta] [Inhabited T.IDMeta]
  [DecidableEq T.IDMeta] [BEq T.IDMeta] [BEq T.Metadata]

private def genMeta : Gen T.Metadata := Arbitrary.arbitrary

private def genConst (env : GenEnv T) (ty : LMonoTy) : Gen (LExpr T.mono) := do
  let m ← genMeta
  match ty with
  | .tcons "bool" [] => pure (.const m (.boolConst (← Gen.chooseAny Bool)))
  | .tcons "int" [] => do
      let n ← Gen.chooseAny (Fin 201)
      pure (.const m (.intConst (Int.ofNat n.val - 100)))
  | .tcons "string" [] => do
      let s ← Arbitrary.arbitrary
      pure (.const m (.strConst s))
  | .tcons "real" [] =>
      if env.ctx.knownTypes.containsName "real" then
        let r ← Arbitrary.arbitrary (α := Int)
        pure (.const m (.realConst (Int.cast r)))
      else throw Gen.genericFailure
  | .bitvec n =>
      if env.ctx.knownTypes.containsName "bitvec" then
        pure (.const m (.bitvecConst n 0))
      else throw Gen.genericFailure
  | _ => pure (.const m (.boolConst true))

private def genBVar (ctx : BCtx) (ty : LMonoTy) : Gen (LExpr T.mono) := do
  let idxs := matchingBinders ctx ty
  match idxs with
  | [] => throw Gen.genericFailure
  | _ => do
    let m ← genMeta
    let i ← Gen.choose Nat 0 (idxs.length - 1) (by omega)
    pure (.bvar m (idxs.getD i.val 0))

private def genFVar (env : GenEnv T) (ty : LMonoTy) : Gen (LExpr T.mono) := do
  let matching := fvarsForType env.fvars ty
  match matching with
  | [] => throw Gen.genericFailure
  | _ => do
    let m ← genMeta
    let i ← Gen.choose Nat 0 (matching.length - 1) (by omega)
    let fv := matching.getD i.val matching.head!
    pure (.fvar m fv.ident none)

private def genLeaf (env : GenEnv T) (ctx : BCtx) (ty : LMonoTy) : Gen (LExpr T.mono) :=
  match ty with
  | .tcons "arrow" [dom, cod] => do
    let m ← genMeta
    let ctx' := shiftCtx ctx ++ [(0, dom)]
    let body ← genLeaf env ctx' cod
    pure (.abs m "" (some dom) body)
  | _ =>
    let gs : List (Nat × Gen (LExpr T.mono)) :=
      [(2, genConst env ty)]
      ++ (if (matchingBinders ctx ty).isEmpty then [] else [(1, genBVar ctx ty)])
      ++ (if (fvarsForType env.fvars ty).isEmpty then [] else [(1, genFVar env ty)])
    Gen.frequency (genConst env ty) gs

/-! ## Core type-directed generator -/

private def genOpApplied (env : GenEnv T) (ty : LMonoTy)
    (mkArgs : List LMonoTy → Gen (List (LExpr T.mono))) : Gen (LExpr T.mono) := do
  let matching := opsForType env.ops ty
  match matching with
  | [] => throw Gen.genericFailure
  | _ => do
    let m ← genMeta
    let idx ← Gen.choose Nat 0 (matching.length - 1) (by omega)
    let op := matching.getD idx.val matching.head!
    let base : LExpr T.mono := .op m op.name none
    let args ← mkArgs op.argTypes
    pure (args.foldl (fun acc arg => .app m acc arg) base)

/-- Generate a bare op node whose full type matches `ty` (used as a value). -/
private def genOpBare (env : GenEnv T) (ty : LMonoTy) : Gen (LExpr T.mono) := do
  let matching := opsWithFullType env.ops ty
  match matching with
  | [] => throw Gen.genericFailure
  | _ => do
    let m ← genMeta
    let idx ← Gen.choose Nat 0 (matching.length - 1) (by omega)
    let op := matching.getD idx.val matching.head!
    pure (.op m op.name none)

private def genTyped (env : GenEnv T) : Nat → BCtx → LMonoTy → Gen (LExpr T.mono)
  | 0, ctx, ty => genLeaf env ctx ty
  | n + 1, ctx, .tcons "bool" [] =>
    let opGens := (if (opsForType env.ops (.tcons "bool" [])).isEmpty then []
                  else [(1, genOpApplied env (.tcons "bool" [])
                    (fun argTys => argTys.mapM (genTyped env n ctx)))])
                  ++ (if (opsWithFullType env.ops (.tcons "bool" [])).isEmpty then []
                  else [(1, genOpBare env (.tcons "bool" []))])
    Gen.frequency (genLeaf env ctx (.tcons "bool" [])) ([
      (4, genLeaf env ctx (.tcons "bool" [])),
      (1, do let t ← genBaseType env.knownBaseTypes
             let a ← genTyped env n ctx t; let b ← genTyped env n ctx t
             let m ← genMeta; pure (.eq m a b)),
      (1, do let c ← genTyped env n ctx .bool
             let a ← genTyped env n ctx .bool; let b ← genTyped env n ctx .bool
             let m ← genMeta; pure (.ite m c a b)),
      (1, do let argTy ← genBaseType env.knownBaseTypes
             let fn ← genTyped env n ctx (.tcons "arrow" [argTy, .bool])
             let arg ← genTyped env n ctx argTy
             let m ← genMeta; pure (.app m fn arg)),
      (1, do let k ← Gen.oneOfWithDefault (pure QuantifierKind.all)
                       [pure QuantifierKind.all, pure QuantifierKind.exist]
             let bTy ← genBaseType env.knownBaseTypes
             let ctx' := shiftCtx ctx ++ [(0, bTy)]
             let body ← genTyped env n ctx' .bool
             let m ← genMeta; pure (.quant m k "" (some bTy) (.bvar m 0) body))]
      ++ opGens)
  | n + 1, ctx, .tcons "arrow" [dom, cod] =>
    let opGens := (if (opsForType env.ops (.tcons "arrow" [dom, cod])).isEmpty
                  then []
                  else [(1, genOpApplied env (.tcons "arrow" [dom, cod])
                    (fun argTys => argTys.mapM (genTyped env n ctx)))])
                  ++ (if (opsWithFullType env.ops (.tcons "arrow" [dom, cod])).isEmpty
                  then []
                  else [(1, genOpBare env (.tcons "arrow" [dom, cod]))])
    Gen.frequency (do let m ← genMeta
                      let body ← genTyped env n (shiftCtx ctx ++ [(0, dom)]) cod
                      pure (.abs m "" (some dom) body)) ([
      (2, do let m ← genMeta
             let body ← genTyped env n (shiftCtx ctx ++ [(0, dom)]) cod
             pure (.abs m "" (some dom) body)),
      (1, do let m ← genMeta
             let x : Identifier T.IDMeta ← Arbitrary.arbitrary
             let env' : GenEnv T := { env with
               fvars := env.fvars ++ [{ ident := x, monoTy := dom }] }
             let body ← genTyped env' n [] cod
             let closed := LExpr.varClose 0 (x, (none : Option LMonoTy)) body
             pure (.abs m "" (some dom) closed)),
      (1, do let c ← genTyped env n ctx .bool
             let a ← genTyped env n ctx (.tcons "arrow" [dom, cod])
             let b ← genTyped env n ctx (.tcons "arrow" [dom, cod])
             let m ← genMeta; pure (.ite m c a b)),
      (1, do let argTy ← genBaseType env.knownBaseTypes
             let fn ← genTyped env n ctx (.tcons "arrow" [argTy, .tcons "arrow" [dom, cod]])
             let arg ← genTyped env n ctx argTy
             let m ← genMeta; pure (.app m fn arg))]
      ++ opGens)
  | n + 1, ctx, ty =>
    let opGens := (if (opsForType env.ops ty).isEmpty then []
                  else [(1, genOpApplied env ty
                    (fun argTys => argTys.mapM (genTyped env n ctx)))])
                  ++ (if (opsWithFullType env.ops ty).isEmpty then []
                  else [(1, genOpBare env ty)])
    Gen.frequency (genLeaf env ctx ty) ([
      (4, genLeaf env ctx ty),
      (1, do let c ← genTyped env n ctx .bool
             let a ← genTyped env n ctx ty; let b ← genTyped env n ctx ty
             let m ← genMeta; pure (.ite m c a b)),
      (1, do let argTy ← genBaseType env.knownBaseTypes
             let fn ← genTyped env n ctx (.tcons "arrow" [argTy, ty])
             let arg ← genTyped env n ctx argTy
             let m ← genMeta; pure (.app m fn arg))]
      ++ opGens)
termination_by fuel => fuel

/-- Fully parameterized generator for well-typed `LExpr T.mono` terms. -/
def mkGen (C : LContext T) (Γ : TContext T.IDMeta) (ty? : Option LMonoTy := none)
    : Gen (LExpr T.mono) := do
  let env := mkGenEnv C Γ
  let size ← Gen.getSize
  let fuel := min size 10
  let ty ← match ty? with
    | some ty => pure ty
    | none => genType env.knownBaseTypes (min fuel 2)
  genTyped env fuel [] ty

end WTG

end -- public meta section
