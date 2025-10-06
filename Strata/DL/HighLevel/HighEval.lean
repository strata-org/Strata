import Strata.DL.HighLevel.HighLevel
import Std.Data.HashMap.Basic
import Lean.Data.AssocList
import Mathlib.Data.Rat.Basic

namespace HighLevel


-- Runtime values with explicit universe level
inductive Value : Type where
  | VUnknown : Value
  | VVoid : Value
  | VBool : Bool → Value
  | VInt : Int → Value
  | VReal : Rat → Value
  | VFloat64 : Float → Value
  | VBoxed : HighType → Value → Value
  | VObject : (type: Identifier) → (field: Lean.AssocList Identifier Value) → Value
  | VNull : Value
  | VClosure : Callable → Value

def Value.asBool! : Value → Bool
  | VBool b => b
  | _ => panic! "expected VBool"

def Value.asInt! : Value → Int
  | VInt i => i
  | _ => panic! "expected VInt"

def Value.asReal! {Rat} : Value → Rat
  | VReal r => r
  | _ => panic! "expected VReal"

def Value.asFloat64! : Value → Float
  | VFloat64 f => f
  | _ => panic! "expected VFloat64"

def Value.asBoxed! : Value → HighType × Value
  | VBoxed ty v => (ty, v)
  | _ => panic! "expected VBoxed"

def Value.asObject! : Value → Identifier × AssocList Identifier Value
  | VObject ty fields => (ty, fields)
  | _ => panic! "expected VObject"

def Value.asClosure! : Value → Callable
  | VClosure c => c
  | _ => panic! "expected VClosure"

structure TypedValue where
  val : Value
  ty : HighType

-- Environment for variable bindings
abbrev Env := AssocList Identifier TypedValue

-- Evaluation result
inductive EvalResult : Type u where
  | Success : TypedValue → Env → EvalResult
  | Return : Value → EvalResult
  | Break : EvalResult
  | Continue : EvalResult
  | TypeError : String → EvalResult
  | VerficationError : VerificationErrorType → String → EvalResult
deriving Nonempty

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
  env.find? name

def voidTv : TypedValue :=
  { val := Value.VVoid, ty := HighType.Void }

/- TODO take type arguments as well, although this needs a type checking/inference phase.
   handle all the operations, and all the types including dynamic. -/
def evalOp (op : Operation) (args : List TypedValue) : Except EvalResult Value :=
  match op with
  | Operation.Add =>
    match args.map fun a => a.ty with
    | [HighType.Dynamic, HighType.Dynamic] => Except.ok <| Value.VInt (a + b)
    | [{ val := Value.VInt a }, { val := Value.VInt b }] => Except.ok <| Value.VInt (a + b)
    | _ => Except.error <| EvalResult.TypeError "Invalid types for Add"
  | Operation.Eq =>
    match args with
    | [Value.VInt a, Value.VInt b] => Except.ok <| Value.VBool (a == b)
    | [Value.VBool a, Value.VBool b] => Except.ok <| Value.VBool (a == b)
    | _ => Except.error "Invalid arguments for Eq"
  | _ => Except.error "Operation not implemented"

-- Main evaluator
partial def eval (expr : StmtExpr) (env : Env) : EvalResult :=
  match expr with
  | StmtExpr.LiteralBool b => EvalResult.Success (TypedValue.mk (Value.VBool b) HighType.Bool) env
  | StmtExpr.LiteralInt i => EvalResult.Success (TypedValue.mk (Value.VInt i) HighType.Int) env
  | StmtExpr.LiteralReal r => EvalResult.Success (TypedValue.mk (Value.VReal r) HighType.Real) env
  | StmtExpr.Identifier name =>
    match lookupVar name env with
    | some tv => EvalResult.Success tv env
    | none => EvalResult.TypeError s!"Undefined variable: {name}"
  | StmtExpr.LocalVariable name _ (some init) =>
    match eval init env with
    | EvalResult.Success tv env' => EvalResult.Success voidTv (env'.insertNew name tv)
    | result => result
  | StmtExpr.LocalVariable name type none => EvalResult.Success voidTv <| env.insertNew name (TypedValue.mk Value.VUnknown type)
/- TODO Support assign to a field as well -/
  | StmtExpr.Assign target value =>
    match eval value env with
    | EvalResult.Success tv env' =>
      match target with
        | StmtExpr.Identifier name =>
          match lookupVar name env' with
          | some _ => EvalResult.Success voidTv (env'.insertNew name (TypedValue.mk tv.val HighType.Dynamic))
          | none => EvalResult.TypeError s!"Undefined variable: {name}"
        | StmtExpr.StaticFieldSelect obj fieldName =>
          match eval obj env' with
          | EvalResult.Success { val := Value.VObject type fields, ty := _ } env'' =>
            let newFields := fields.insertNew fieldName tv.val
            let newObj := Value.VObject type newFields
            EvalResult.Success voidTv env''.insertNew "_temp" (TypedValue.mk newObj HighType.Dynamic) -- TODO update variable holding the object
          | EvalResult.Success _ _ => EvalResult.TypeError "Target is not an object"
          | result => result

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
