/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DDM.AST

/-!
Runtime support for converting AST representations back to generated types.
Defines the `OfAstM` error monad and argument-parsing combinators used by
the `ofAst` functions that `#strata_gen` emits.
-/

public section
namespace Strata

class HasEta (α : Type u) (β : outParam (Type v)) where
  bvar : Nat → α
  lambda : String → β → α → α

def etaExpand {E T} [HasEta E T]
    (argTypes : Array (String × T)) (provided : Nat) (e : E) : E :=
  if argTypesP  : provided < argTypes.size then
    let b := argTypes[argTypes.size - 1]
    let e := HasEta.lambda b.fst b.snd e
    etaExpand argTypes.pop provided e
  else
    e

@[expose] def OfAstM (α : Type _) := Except String α

instance {α} [ToString α] : ToString (OfAstM α) where
  toString e := private
    match e with
    | .error e => e
    | .ok r => toString r

instance {α} [Repr α] : Repr (OfAstM α) where
  reprPrec e prec := private
    match e with
    | .error e => Repr.addAppParen ("error " ++ reprArg e) prec
    | .ok r => Repr.addAppParen ("ok " ++ reprArg r) prec

namespace OfAstM

instance : Monad OfAstM := inferInstanceAs (Monad (Except _))

/--
Thrown when an expression is provided but not expected.
-/
def throwUnknownExpr (tp : QualifiedIdent) (e : Expr) : OfAstM α :=
  Except.error s!"Unknown expr {repr e} when parsing as {tp}."

/--
Thrown when an expression is provided but not expected.
-/
def throwUnknownType (e : TypeExpr) : OfAstM α :=
  Except.error s!"Unknown type {repr e}."

/--
Raise error when passed an argument that is not an expression when expression expected.
-/
def throwExpected {Ann α} [Repr Ann] (cat : String) (a : ArgF Ann) : OfAstM α :=
  Except.error s!"Expected {cat} {repr a}."

/--
Raise error when passed an argument that is not an expression when expression expected.
-/
def throwExpectedExpr {Ann α} [Repr Ann] (a : ArgF Ann) : OfAstM α :=
  throwExpected "expression" a

/--
Raise error when passed an argument that is not an expression when expression expected.
-/
def throwExpectedOperation (a : Arg) : OfAstM α :=
  throwExpected "operation" a

def throwUnexpectedBvar (tp : QualifiedIdent) : OfAstM α :=
  Except.error s!"{tp} has unexpected bound variable."

def throwUnexpectedArgCount (tp : QualifiedIdent) (expected : Nat) (actual : Nat)
  : OfAstM α :=
  Except.error s!"{tp} expected {expected} arguments when {actual} provided."

def throwUnknownIdentifier (tp : QualifiedIdent) (f: QualifiedIdent) : OfAstM α :=
  Except.error s!"{tp} given unknown operator {f}."

protected def checkTypeArgCount
    (expected : Nat)
    (args : Array α)
    : OfAstM (PLift (args.size = expected)) :=
  if p : args.size = expected then
    return .up p
  else
    .throwUnexpectedArgCount q`Init.Type expected args.size

protected def checkArgCount
    (tp : QualifiedIdent)
    (expected : Nat)
    (args : Array α)
    : OfAstM (PLift (args.size = expected)) :=
  if p : args.size = expected then
    return .up p
  else
    .throwUnexpectedArgCount tp expected args.size

protected def checkEtaExprArgCount
    {Tp : Type _}
    (tp : QualifiedIdent)
    (expected : Array (String × Tp))
    (args : Array Arg)
    : OfAstM (PLift (args.size ≤ expected.size)) :=
  if p : args.size ≤ expected.size then
    return .up p
  else
    .throwUnexpectedArgCount tp expected.size args.size

def ofExpressionM {α β} [Repr α] [SizeOf α]
    (val : ArgF α)
    (act : ∀(e : ExprF α), sizeOf e < sizeOf val → OfAstM β)
    : OfAstM β :=
  match val with
  | .expr a1 => act a1 (by decreasing_tactic)
  | a => .throwExpected "expression" a

def ofTypeM {α β} [Repr α] [SizeOf α]
      (val : ArgF α)
      (act : ∀(e : TypeExprF α), sizeOf e < sizeOf val → OfAstM β)
      : OfAstM β :=
  match val with
  | .type a1 => act a1 (by decreasing_tactic)
  | a => .throwExpected "type" a

def ofOperationM {α β} [Repr α] [SizeOf α]
        (val : ArgF α)
        (act : ∀(o : OperationF α), sizeOf o < sizeOf val → OfAstM β)
      : OfAstM β :=
  match val with
  | .op a1 => act a1 (by decreasing_tactic)
  | a => .throwExpected "operation" a

def ofIdentM {α} [Repr α] : ArgF α → OfAstM String
| .ident _ val => pure val
| a => .throwExpected "identifier" a

def ofAnnIdentM {α} [Repr α] : ArgF α → OfAstM (Ann String α)
| .ident ann val => pure { ann := ann, val := val }
| a => .throwExpected "identifier" a

def ofNumM {α} [Repr α] : ArgF α → OfAstM Nat
| .num _ val => pure val
| a => .throwExpected "numeric literal" a

def ofAnnNumM {α} [Repr α] : ArgF α → OfAstM (Ann Nat α)
| .num ann val => pure { ann := ann, val := val }
| a => .throwExpected "numeric literal" a

def ofDecimalM {α} [Repr α] : ArgF α → OfAstM Decimal
| .decimal _ val => pure val
| a => .throwExpected "scientific literal" a

def ofAnnDecimalM {α} [Repr α] : ArgF α → OfAstM (Ann Decimal α)
| .decimal ann val => pure { ann := ann, val := val }
| a => .throwExpected "scientific literal" a

def ofStrlitM {α} [Repr α] : ArgF α → OfAstM String
| .strlit _ val => pure val
| a => .throwExpected "string literal" a

def ofAnnStrlitM {α} [Repr α] : ArgF α → OfAstM (Ann String α)
| .strlit ann val => pure { ann := ann, val := val }
| a => .throwExpected "string literal" a

def ofBytesM {α} [Repr α] : ArgF α → OfAstM ByteArray
| .bytes _ val => pure val
| a => .throwExpected "byte array" a

def ofAnnBytesM {α} [Repr α] : ArgF α → OfAstM (Ann ByteArray α)
| .bytes ann val => pure { ann := ann, val := val }
| a => .throwExpected "byte array" a

/-- Convert Ann Bool to OperationF -/
def toAstBool {α} [Inhabited α] (v : Ann Bool α) : OperationF α :=
  if v.val then
    ⟨v.ann, q`Init.boolTrue, #[]⟩
  else
    ⟨v.ann, q`Init.boolFalse, #[]⟩

/-- Convert OperationF to Ann Bool -/
def ofAstBool {α} [Inhabited α] [Repr α] (op : OperationF α) : OfAstM (Ann Bool α) :=
  match op.name with
  | q`Init.boolTrue =>
    if op.args.size = 0 then
      pure ⟨op.ann, true⟩
    else
      .error s!"boolTrue expects 0 arguments, got {op.args.size}"
  | q`Init.boolFalse =>
    if op.args.size = 0 then
      pure ⟨op.ann, false⟩
    else
      .error s!"boolFalse expects 0 arguments, got {op.args.size}"
  | _ =>
    .error s!"Unknown Bool operator: {op.name}"

def ofBoolM {α} [Inhabited α] [Repr α] : ArgF α → OfAstM Bool
| .op op => Ann.val <$> ofAstBool op
| a => .throwExpected "boolean" a

def ofAnnBoolM {α} [Inhabited α] [Repr α] : ArgF α → OfAstM (Ann Bool α)
| .op op => ofAstBool op
| a => .throwExpected "boolean" a

def ofOptionM {α β} [Repr α] [SizeOf α]
      (arg : ArgF α)
      (act : ∀(e : ArgF α), sizeOf e < sizeOf arg → OfAstM β)
      : OfAstM (Ann (Option β) α) :=
  match arg with
  | .option ann mv =>
    match mv with
    | none =>
      pure { ann := ann, val := none }
    | some v =>
      (fun v => { ann := ann, val := some v }) <$> act v (by decreasing_tactic)
  | _ => throwExpected "option" arg

def ofSeqM {α β} [Repr α] [SizeOf α]
      (sep : SepFormat)
      (arg : ArgF α)
      (act : ∀(e : ArgF α), sizeOf e < sizeOf arg → OfAstM β)
      : OfAstM (Ann (Array β) α) :=
  match arg with
  | .seq ann sep' a =>
    if sep == sep' then do
      let val ← a.attach.mapM fun ⟨v, vIn⟩ =>
        act v (by decreasing_tactic)
      pure { ann := ann, val := val }
    else
      throwExpected sep.toString arg
  | _ => throwExpected sep.toString arg

/--
Distinguishes between a type parameter (category reference) and a type
expression in Init.TypeP, applying the appropriate handler.
-/
def matchTypeParamOrType {Ann α} [Repr Ann] (a : ArgF Ann)
    (onTypeParam : Ann → α) (onType : TypeExprF Ann → OfAstM α)
    : OfAstM α :=
  match a with
  | .cat cat =>
    if cat.name == q`Init.Type && cat.args.isEmpty then
      pure (onTypeParam cat.ann)
    else
      .throwExpected "Type parameter or type expression" a
  | .type tp => onType tp
  | _ => .throwExpected "Type parameter or type expression" a

end Strata.OfAstM
end
