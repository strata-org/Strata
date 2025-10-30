/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
This file defines the behavior of both a type checker and a verifier for the Laurel language.
Both are defined using the 'eval' function. It will only return a single type or verification error at a time.

TODO: implicit casting from primitives types to Dynamic
-/
import Strata.DL.HighStrata.HighStrata
import Std.Data.HashMap.Basic
import Lean.Data.AssocList

namespace HighLevel

open Std
open Lean
open HighLevel

mutual
-- Runtime values with explicit universe level
inductive Value : Type where
  | VUnknown : Value
  | VVoid : Value
  | VBool : Bool → Value
  | VInt : Int → Value
  -- | VReal : Rat → Value -- Skipped for now, as Lean's Rat requires importing MathLib
  | VFloat64 : Float → Value
  | VBoxed : TypedValue → Value
  | VObject : (type: Identifier) → (field: AssocList Identifier Value) → Value
  | VNull : Value
  | VClosure : Callable → Value

structure TypedValue where
  val : Value
  ty : HighType

end

instance : Inhabited TypedValue where
  default := { val := Value.VVoid, ty := HighType.TVoid }

def Value.asBool! : Value → Bool
  | VBool b => b
  | _ => panic! "expected VBool"

def Value.asInt! : Value → Int
  | VInt i => i
  | _ => panic! "expected VInt"

def Value.asFloat64! : Value → Float
  | VFloat64 f => f
  | _ => panic! "expected VFloat64"

def Value.asBoxed! : Value → TypedValue
  | VBoxed tv => tv
  | _ => panic! "expected VBoxed"

def Value.asObject! : Value → Identifier × AssocList Identifier Value
  | VObject ty fields => (ty, fields)
  | _ => panic! "expected VObject"

-- Environment for variable bindings
structure Env where
  locals: List (AssocList Identifier TypedValue)
  statics: HashMap Identifier Callable
  heap: HashMap Int Value
  returnType : HighType

inductive VerificationErrorType : Type where
  | PreconditionFailed : VerificationErrorType
  | PostconditionFailed : VerificationErrorType
  | InvariantFailed : VerificationErrorType
  | DecreasesFailed : VerificationErrorType
  | ReadEffectFailed : VerificationErrorType

-- Evaluation result
inductive EvalResult (value: Type u) : Type u where
  | Success : value → EvalResult value
  | Return : Value → EvalResult value
  | Exitting : (target: Identifier) → EvalResult value
  | TypeError : String → EvalResult value
  | VerficationError : VerificationErrorType → String → EvalResult value

def Eval (value: Type u): Type u := Env → EvalResult value × Env
def getLocal (name: Identifier) : Eval TypedValue :=
  let rec getInLocal (locals: List (AssocList Identifier TypedValue)) :=
    match locals with
    | [] => none
    | top :: rest =>
      match top.find? name with
      | some result => some result
      | none => getInLocal rest

  fun env => match getInLocal env.locals with
    | some result => (EvalResult.Success result, env)
    | none => (EvalResult.TypeError s!"Undefined variable: {name}", env)

def getEnv : Eval Env := fun env => (EvalResult.Success env, env)
def setEnv (newEnv: Env) : Eval PUnit := fun _ => (EvalResult.Success PUnit.unit, newEnv)

def voidTv : TypedValue :=
  { val := Value.VVoid, ty := HighType.TVoid }

def setLocal (name: Identifier) (typedValue: TypedValue): Eval PUnit :=
  fun env => (EvalResult.Success PUnit.unit, { env with locals := (env.locals.head!.insert name typedValue :: env.locals.tail) })

def pushStack: Eval PUnit :=
  fun env => (EvalResult.Success PUnit.unit, { env with locals := AssocList.empty :: env.locals })
def popStack: Eval PUnit :=
  fun env => (EvalResult.Success PUnit.unit, { env with locals := env.locals.tail })

def assertBool (tv: TypedValue) : Eval PUnit := fun env =>
  if (tv.ty.isBool) then
    (EvalResult.TypeError "Precondition must be boolean", env)
  else if (tv.val.asBool!) then
    (EvalResult.VerficationError VerificationErrorType.PreconditionFailed "Precondition does not hold", env)
  else
    (EvalResult.Success PUnit.unit, env)

instance : Monad Eval where
  pure x := fun e => (EvalResult.Success x, e)
  bind := fun r f => fun env =>
    let (r', env') := r env
    match r' with
    | EvalResult.Success sm => f sm env'
    | EvalResult.Return v => (EvalResult.Return v, env')
    | EvalResult.Exitting target => (EvalResult.Exitting target, env')
    | EvalResult.TypeError msg => (EvalResult.TypeError msg, env')
    | EvalResult.VerficationError et msg => (EvalResult.VerficationError et msg, env')

def withResult {u: Type} (r : EvalResult u) : Eval u :=
  fun env => (r, env)

def evalOpWithoutDynamic (op : Operation) (args : List TypedValue) : Except (EvalResult TypedValue) TypedValue :=
  let argTypes := args.map (fun a => a.ty)
  match args with
  | [arg1, arg2] =>
    match op with
    | Operation.Add =>
        match argTypes with
        | [HighType.TInt, HighType.TInt] => Except.ok <| TypedValue.mk (Value.VInt (arg1.val.asInt! + arg2.val.asInt!)) HighType.TInt
        | [HighType.TFloat64, HighType.TFloat64] => Except.ok <| TypedValue.mk (Value.VFloat64 (arg1.val.asFloat64! + arg2.val.asFloat64!)) HighType.TFloat64
        -- TOOD add other types
        | _ => Except.error <| EvalResult.TypeError "Invalid types for Add"

    | Operation.Eq =>
      match argTypes with
      | [HighType.TInt, HighType.TInt] => Except.ok <| { val := Value.VBool (arg1.val.asInt! == arg2.val.asInt!), ty := HighType.TBool }
      | [HighType.TBool, HighType.TBool] => Except.ok <| { val := Value.VBool (arg1.val.asBool! == arg2.val.asBool!), ty := HighType.TBool }
      | _ => Except.error <| EvalResult.TypeError "Invalid types for Eq"
    | _ => Except.error <| EvalResult.TypeError "Operation not implemented"
  | _ => Except.error <| EvalResult.TypeError s!"No operator with {args.length} arguments"

def evalOp (op : Operation) (args : List TypedValue) : Except (EvalResult TypedValue) TypedValue :=
  if (args.all fun a => a.ty.isDynamic) then
    match evalOpWithoutDynamic op (args.map fun a => a.val.asBoxed!) with
      | Except.ok v => Except.ok v
      | Except.error (EvalResult.TypeError msg) =>
          Except.error (EvalResult.VerficationError VerificationErrorType.PreconditionFailed msg)
      | Except.error e => Except.error e
  else
    evalOpWithoutDynamic op args

partial def eval (expr : StmtExpr) : Eval TypedValue :=
  match expr with
-- Expressions
  | StmtExpr.LiteralBool b => pure <| TypedValue.mk (Value.VBool b) HighType.TBool
  | StmtExpr.LiteralInt i => pure <| TypedValue.mk (Value.VInt i) HighType.TInt
  | StmtExpr.Identifier name => getLocal name

  | StmtExpr.IfThenElse condExpr thenBranch elseBranch => do
    let cond <- eval condExpr
    if (cond.ty.isBool) then
      withResult <| EvalResult.TypeError "Condition must be boolean"
    else
      if cond.val.asBool! then eval thenBranch else
        match elseBranch with
        | some elseStmt => eval elseStmt
        | none => pure voidTv

  | StmtExpr.PrimitiveOp op args => do
    let evalArgs ← args.mapM (fun arg => eval arg)
    match evalOp op evalArgs with
    | Except.ok val => pure val
    | Except.error msg => withResult msg
  | StmtExpr.StaticInvocation callee argumentsExprs => do
    let env ← getEnv
    match env.statics.get? callee with
      | none => withResult <| EvalResult.TypeError s!"Undefined static method: {callee}"
      | some callable => do
        if callable.inputs.length != argumentsExprs.length then
          withResult <| (EvalResult.TypeError s!"Static invocation of {callee} with wrong number of arguments")
        else
          let arguments ← argumentsExprs.mapM (fun arg => eval arg)
          let mod ← match callable.purity with
            | Purity.Impure modifies => eval modifies
            | Purity.Pure reads => panic! "not implemented" -- pure { val := [], ty := }
          let env ← getEnv
          setEnv { env with heap := env.heap  } -- TODO: apply mod

          pushStack
          arguments.zip callable.inputs |>.forM (fun (arg, param) =>
              if param.type != arg.ty then
                withResult <| EvalResult.TypeError s!"Static invocation of {callee} with wrong type for argument {param.name}"
              else
                setLocal param.name arg
            )
          let precondition ← eval callable.precondition
          assertBool precondition
          -- TODO, handle decreases

          let result: TypedValue ← match callable.body with
            | Body.Transparent bodyExpr => do
              let transparantResult ← eval bodyExpr
              if transparantResult.ty != callable.output then
                withResult <| EvalResult.TypeError s!"Static invocation of {callee} with wrong return type"
              else
                pure transparantResult
            | Body.Opaque (postcondition: StmtExpr) _ => panic! "not implemented: opaque body"
            | Body.Abstract (postcondition: StmtExpr) => panic! "not implemented: opaque body"
          popStack
          pure result

-- Statements
  | StmtExpr.Block stmts label => evalBlock label stmts

-- Support locals
  | StmtExpr.LocalVariable name _ (some init) => do
      let value ← eval init
      setLocal name value
      return voidTv
  | StmtExpr.LocalVariable name type none => do
    setLocal name (TypedValue.mk Value.VUnknown type)
    return voidTv
  | StmtExpr.Assign (StmtExpr.Identifier localName) valueExpr => do
    let value ← eval valueExpr
    let oldTypedValue ← getLocal localName
    setLocal localName (TypedValue.mk value.val oldTypedValue.ty)
    pure voidTv
-- Jumps
  | StmtExpr.Return (some valExpr) => do
    let tv ← eval valExpr
    withResult (EvalResult.Return tv.val)
  | StmtExpr.Return none => fun env => (EvalResult.Success { val := Value.VVoid, ty := env.returnType }, env)
  | StmtExpr.While _ none _ _  => withResult <| EvalResult.TypeError "While invariant was not derived"
  | StmtExpr.While _ _ none _  => withResult <| EvalResult.TypeError "While decreases was not derived"
  | StmtExpr.While condExpr (some invariantExpr) (some decreasedExpr) bodyExpr => do
    let rec loop : Eval TypedValue := do
      let cond ← eval condExpr
      if (cond.ty.isBool) then
        withResult <| EvalResult.TypeError "Condition must be boolean"
      else if cond.val.asBool! then
        let invariant ← eval invariantExpr
        if (invariant.ty.isBool) then
          withResult <| EvalResult.TypeError "Invariant must be boolean"
        else if (!invariant.val.asBool!) then
          withResult <| EvalResult.VerficationError VerificationErrorType.InvariantFailed "While invariant does not hold"
        else
        -- TODO handle decreases
          fun env => match eval bodyExpr env with
            | (EvalResult.Success _, env') => loop env'
            | other => other
      else
        pure voidTv
    loop
  | StmtExpr.Exit target => withResult <| EvalResult.Exitting target

-- Support non-heap objects
  | StmtExpr.PureFieldUpdate _ _ _ => panic! "not implemented: PureFieldUpdate"
  | KnownFieldSelect _ _ => panic! "not implemented: StaticFieldSelect"

-- Support heap objects
  | StmtExpr.Assign (KnownFieldSelect objExpr fieldName) valueExpr =>
    panic! "not implemented"
  -- do
  --     let objTv ← eval objExpr
  --     match objTv.ty with
  --     | HighType.UserDefined targetName => ()
  --     if (objTv.ty != HighType.) then
  --       return EvalResult.TypeError "Target object must be of type Dynamic"
  --     match objTv.typ with
  --     | EvalResult.Success { val := Value.VObject type fields, ty := _ } env'' =>
  --       let newFields := fields.insertNew fieldName tv.val
  --       let newObj := Value.VObject type newFields
  --       EvalResult.Success voidTv env''.insertNew "_temp" (TypedValue.mk newObj HighType.Dynamic) -- TODO update variable holding the object
  --     | EvalResult.Success _ _ => EvalResult.TypeError "Target is not an object"
  --     | result => result
  --    | _ => EvalResult.TypeError "Invalid assignment target"
  | StmtExpr.Assign (StmtExpr.DynamicFieldAccess objExpr fieldName) valueExpr => panic! "not implemented"
  | StmtExpr.Assign _ valueExpr => withResult <| EvalResult.TypeError "Invalid assignment target"

-- Instance related
  | StmtExpr.This => panic! "not implemented: This"
  | StmtExpr.IsType _ _ _ => panic! "not implemented: IsType"
  | StmtExpr.InstanceInvocation _ _ _ => panic! "not implemented: InstanceInvocation"

-- Dynamic
  | StmtExpr.Closure _ => panic! "not implemented: Closure"
  | StmtExpr.DynamicInvocation _ _ => panic! "not implemented: DynamicInvocation"
  | StmtExpr.DynamicFieldAccess _ _ => panic! "not implemented: DynamicFieldAccess"
  | StmtExpr.DynamicFieldUpdate _ _ _ => panic! "not implemented: DynamicFieldUpdate"

-- Verification statements
  | StmtExpr.Assert condExpr => do
    let cond ← eval condExpr
    if cond.ty.isBool then
      withResult <| EvalResult.TypeError "Condition must be boolean"
    else if cond.val.asBool! then
      pure voidTv
    else
      withResult <| EvalResult.VerficationError VerificationErrorType.PreconditionFailed "Assertion failed"
  | StmtExpr.Assume _ => panic! "not implemented: Assume"
  | StmtExpr.ProveBy _ _ => panic! "not implemented: ProveBy"
  | StmtExpr.Assigned _ => panic! "not implemented: Assigned"

-- Heap verification statements
  | StmtExpr.Old _ => panic! "not implemented: Old"
  | StmtExpr.Fresh _ => panic! "not implemented: Fresh"

-- Construction
  | StmtExpr.Create _ => panic! "not implemented: Create"
  | StmtExpr.Complete _ => panic! "not implemented: Complete"

-- Used for incomplete code during development
  | StmtExpr.Hole => pure <| TypedValue.mk Value.VUnknown HighType.Dynamic
  | _ => panic! "not implemented"


where
  evalBlock (labelOption: Option Identifier) (stmts : List StmtExpr) : Eval TypedValue :=
    match stmts with
    | [] => pure <| TypedValue.mk Value.VVoid HighType.TVoid
    | stmt :: rest => fun env => match eval stmt env with
      | (EvalResult.Exitting target, env') =>
        let targetsMe := some target == labelOption
        if targetsMe then
          (EvalResult.Success voidTv, env')
        else
          evalBlock labelOption rest env'
      | (EvalResult.Success _, env') => evalBlock labelOption rest env'
      | other => other

end HighLevel
