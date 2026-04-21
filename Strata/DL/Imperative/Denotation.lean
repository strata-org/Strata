/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.Stmt

namespace Imperative

structure TypedId (Id : Type) where
  name : Id
  ty : Type

-- TODO: look into how this connects with partial fixpoints
class MonadIter (m : Type u → Type v) extends Monad m where
  iter : {A B : Type u} -> (f : A -> m (A ⊕ B)) -> (a₀ : A) -> m B

class MonadMemRead (Id : Type) (m : Type → Type) extends Monad m where
  read : (id : TypedId Id) → m id.ty

class MonadMemWrite (Id : Type) (m : Type → Type) extends Monad m where
  write : (id : TypedId Id) → (v : id.ty) → m Unit

class MonadMemory (Id : Type) (m : Type → Type) extends MonadMemRead Id m, MonadMemWrite Id m where

class MonadAssert (m : Type → Type) extends Monad m where
  assert : Prop → m Unit

class MonadAssume (m : Type → Type) extends Monad m where
  assume : Prop → m Unit

class MonadAssertAssume (m : Type → Type) extends MonadAssert m, MonadAssume m where

class MonadNondet (m : Type → Type) extends Monad m where
  choose : (t : Type) → m t

def whileLoop {m} [MonadIter m] (c : m Bool) (body : m Unit) : m Unit :=
  MonadIter.iter (fun () => do
    if (<- c) then do
      body
      return .inl ()
    else
      return .inr ()
  ) ()

structure DenotationContext (P : PureExpr) (m : Type → Type) [MonadMemRead P.Ident m] where
  env : P.Ident → Type
  denoteExpr : P.Expr → (t : Type) → m t

def denoteExprOrNondet
  [MonadNondet m] [MonadMemRead P.Ident m] :
  DenotationContext P m → ExprOrNondet P → (ty : Type) → m ty
| ctx, .det e,  ty => ctx.denoteExpr e ty
| _,   .nondet, ty => MonadNondet.choose ty

def writeExprOrNondet
  {m}
  {P : PureExpr}
  [MonadMemory P.Ident m]
  [MonadNondet m]
  (ctx : DenotationContext P m)
  (x : P.Ident)
  (e? : ExprOrNondet P) : m Unit := do
    let ty := ctx.env x
    MonadMemory.write ⟨ x, ty ⟩ (← denoteExprOrNondet ctx e? ty)

def denoteCmd
  {m}
  {P : PureExpr}
  [MonadMemory P.Ident m]
  [MonadAssertAssume m]
  [MonadNondet m]
  (ctx : DenotationContext P m)
  (c : Cmd P) : m Unit :=
  match c with
  | .assert _ e _  => do MonadAssert.assert (← ctx.denoteExpr e Bool)
  | .assume _ e _  => do MonadAssume.assume (← ctx.denoteExpr e Bool)
  | .set x e? _    => writeExprOrNondet ctx x e?
  | .init x _ e? _ => writeExprOrNondet ctx x e?
  | .cover _ _ _   => pure ()

mutual

def denoteStmt
  {m CmdT}
  {P : PureExpr}
  [MonadMemory P.Ident m]
  [MonadAssertAssume m]
  [MonadNondet m]
  [MonadIter m]
  [MonadExcept (Option String) m]
  (ctx : DenotationContext P m)
  (denoteCmd : DenotationContext P m → CmdT → m Unit)
  (s : Stmt P CmdT) : m Unit :=
  match s with
  | .cmd c => denoteCmd ctx c
  | .block l ss _ =>
    MonadExcept.tryCatch
      (denoteStmts ctx denoteCmd ss)
      (fun e =>
        match e with
        | .some el => if el == l then return () else MonadExcept.throw e
        | .none => return ())
  | .exit l? _ => MonadExcept.throw l?
  | .ite c? t e _ => do
    if (← denoteExprOrNondet ctx c? Bool) then
      denoteStmts ctx denoteCmd t
    else
      denoteStmts ctx denoteCmd e
  | .loop c? _ _ ss _ =>
    MonadExcept.tryCatch
      (whileLoop (denoteExprOrNondet ctx c? Bool) (denoteStmts ctx denoteCmd ss))
      (fun e =>
        match e with
        -- TODO: if loops had labels, we could potentially catch an
        -- exit with a label here. Since they don't, only an exit
        -- without a label can lead to early loop termination.
        | .some _ => MonadExcept.throw e
        | .none => return ())
  | .funcDecl _ _ => return () -- TODO: Not supported for now
  | .typeDecl _ _ => return () -- TODO: Not supported for now

def denoteStmts
  {m CmdT}
  {P : PureExpr}
  [MonadMemory P.Ident m]
  [MonadAssertAssume m]
  [MonadNondet m]
  [MonadIter m]
  [MonadExcept (Option String) m]
  (ctx : DenotationContext P m)
  (denoteCmd : DenotationContext P m -> CmdT → m Unit)
  (ss : List (Stmt P CmdT)) : m Unit :=
  -- TODO: would like ss.forM (...), but need an explicit termination proof for that
  match ss with
  | [] => return ()
  | s :: rest => do
    denoteStmt ctx denoteCmd s
    denoteStmts ctx denoteCmd rest

end
