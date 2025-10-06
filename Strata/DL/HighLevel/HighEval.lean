import Strata.DL.HighLevel.HighLevel
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
  locals: AssocList Identifier TypedValue
  heap: HashMap Int Value

-- Evaluation result
inductive EvalResult : Type u where
  | Success : TypedValue → Env → EvalResult
  | Return : Value → EvalResult
  | Break : EvalResult
  | Continue : EvalResult
  | TypeError : String → EvalResult
  | VerficationError : VerificationErrorType → String → EvalResult
deriving Nonempty, Inhabited

inductive VerificationErrorType : Type where
  | PreconditionFailed : String → VerificationErrorType
  | PostconditionFailed : String → VerificationErrorType
  | InvariantFailed : String → VerificationErrorType
  | DecreasesFailed : String → VerificationErrorType
  | ReadEffectFailed : String → VerificationErrorType

def bind : EvalResult → (TypedValue → Env → EvalResult) → EvalResult
  | EvalResult.Success tv env, f => f tv env
  | EvalResult.Return v, _ => EvalResult.Return v
  | EvalResult.Break, _ => EvalResult.Break
  | EvalResult.Continue, _ => EvalResult.Continue
  | EvalResult.TypeError msg, _ => EvalResult.TypeError msg
  | EvalResult.VerficationError et msg, _ => EvalResult.VerficationError et msg

-- Helper functions
def lookupVar (name : Identifier) (env : Env) : Option TypedValue :=
  env.locals.find? name

def voidTv : TypedValue :=
  { val := Value.VVoid, ty := HighType.TVoid }

def evalOpWithoutDynamic (op : Operation) (args : List TypedValue) : Except EvalResult Value :=
  let argTypes := args.map (fun a => a.ty)
  match args with
  | [arg1, arg2] =>
    match op with
    | Operation.Add =>
        match argTypes with
        | [HighType.TInt, HighType.TInt] => Except.ok <| Value.VInt (arg1.val.asInt! + arg2.val.asInt!)
        | [HighType.TFloat64, HighType.TFloat64] => Except.ok <| Value.VFloat64 (arg1.val.asFloat64! + arg2.val.asFloat64!)
        -- TOOD add other types
        | _ => Except.error <| EvalResult.TypeError "Invalid types for Add"

    | Operation.Eq =>
      match argTypes with
      | [HighType.TInt, HighType.TInt] => Except.ok <| Value.VBool (arg1.val.asInt! == arg2.val.asInt!)
      | [HighType.TBool, HighType.TBool] => Except.ok <| Value.VBool (arg1.val.asBool! == arg2.val.asBool!)
      | _ => Except.error <| EvalResult.TypeError "Invalid types for Eq"
    | _ => Except.error <| EvalResult.TypeError "Operation not implemented"
  | _ => Except.error <| EvalResult.TypeError s!"No operator with {args.length} arguments"

def evalOp (op : Operation) (args : List TypedValue) : Except EvalResult Value :=
  if (args.all fun a => a.ty.isDynamic) then
    match evalOpWithoutDynamic op (args.map fun a => a.val.asBoxed!) with
      | Except.ok v => Except.ok v
      | Except.error (EvalResult.TypeError msg) =>
          Except.error (EvalResult.VerficationError VerificationErrorType.PreconditionFailed msg)
      | Except.error e => Except.error e
  else
    evalOpWithoutDynamic op args

-- Main evaluator
partial def eval (expr : StmtExpr) (env : Env) : EvalResult :=
  match expr with
  | StmtExpr.LiteralBool b => EvalResult.Success (TypedValue.mk (Value.VBool b) HighType.TBool) env
  | StmtExpr.LiteralInt i => EvalResult.Success (TypedValue.mk (Value.VInt i) HighType.TInt) env
  | StmtExpr.LiteralReal r => panic! "not implemented" -- EvalResult.Success (TypedValue.mk (Value.VReal r) HighType.TReal) env
  | StmtExpr.Identifier name =>
    match lookupVar name env with
    | some tv => EvalResult.Success tv env
    | none => EvalResult.TypeError s!"Undefined variable: {name}"
  | StmtExpr.LocalVariable name _ (some init) =>
    match eval init env with
    | EvalResult.Success tv env' => EvalResult.Success voidTv { env' with locals := env'.locals.insertNew name tv }
    | result => result
  | StmtExpr.LocalVariable name type none => EvalResult.Success voidTv
      { env with locals := env.locals.insertNew name (TypedValue.mk Value.VUnknown type) }
  | StmtExpr.Assign target value =>
    match eval value env with
    | EvalResult.Success tv env' =>
      match target with
        | StmtExpr.Identifier name =>
          match lookupVar name env' with
          | some _ => EvalResult.Success voidTv (env'.locals.insertNew name (TypedValue.mk tv.val HighType.Dynamic))
          | none => EvalResult.TypeError s!"Undefined variable: {name}"
        | StmtExpr.StaticFieldSelect obj fieldName =>
          match eval obj env' with
          | EvalResult.Success { val := Value.VObject type fields, ty := _ } env'' =>
            let newFields := fields.insertNew fieldName tv.val
            let newObj := Value.VObject type newFields
            EvalResult.Success voidTv env''.insertNew "_temp" (TypedValue.mk newObj HighType.Dynamic) -- TODO update variable holding the object
          | EvalResult.Success _ _ => EvalResult.TypeError "Target is not an object"
          | result => result
/- TODO Support DynamicFieldSelect as well -/

        | _ => EvalResult.TypeError "Invalid assignment target"
    | result => result

  | StmtExpr.Block stmts => evalBlock stmts env
  | StmtExpr.IfThenElse cond thenBranch elseBranch =>
    match eval cond env with
    | EvalResult.Success (Value.VBool true) env' => eval thenBranch env'
    | EvalResult.Success (Value.VBool false) env' =>
      match elseBranch with
      | some elseStmt => eval elseStmt env'
      | none => EvalResult.Success Value.VVoid env'
    | EvalResult.Success _ _ => EvalResult.Error "Condition must be boolean"
    | result => result
  | StmtExpr.PrimitiveOp op args =>
    let evalArgs := args.map (fun arg => match eval arg env with
      | EvalResult.Success v _ => v
      | _ => Value.VVoid) /- TODO handle errors and control flow -/
    match evalOp op evalArgs with
    | Except.ok val => EvalResult.Success val env
    | Except.error msg => EvalResult.Error msg
  | StmtExpr.Return (some val) =>
    match eval val env with
    | EvalResult.Success v _ => EvalResult.Return v
    | result => result
  | StmtExpr.Return none => EvalResult.Return Value.VVoid
  | StmtExpr.Create typeName => EvalResult.Success (Value.VObject typeName AssocList.nil) env
  | StmtExpr.Hole => EvalResult.Success Value.VVoid env
  | _ => EvalResult.Error "Unsupported expression"

where
  evalBlock (stmts : List StmtExpr) (env : Env) : EvalResult :=
    match stmts with
    | [] => EvalResult.Success Value.VVoid env
    | stmt :: rest =>
      match eval stmt env with
      | EvalResult.Success _ env' => evalBlock rest env'
      | result => result

end HighLevel
