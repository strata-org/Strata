/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DDM.AST
public import Strata.DDM.HNF
import all Strata.DDM.Util.Array

public section
namespace Strata

class HasEta (α : Type u) (β : outParam (Type v)) where
  bvar : Nat → α
  lambda : String → β → α → α

def etaExpand {E T} [HasEta E T] (argTypes : Array (String × T)) (provided : Nat) (e : E) : E :=
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

def ofExpressionM {α β} [Repr α] [SizeOf α] (val : ArgF α) (act : ∀(e : ExprF α), sizeOf e < sizeOf val → OfAstM β)
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

def ofIdentM {α} [Repr α] : ArgF α → OfAstM (Ann String α)
| .ident ann val => pure { ann := ann, val := val }
| a => .throwExpected "identifier" a

def ofNumM {α} [Repr α] : ArgF α → OfAstM (Ann Nat α)
| .num ann val => pure { ann := ann, val := val }
| a => .throwExpected "numeric literal" a

def ofDecimalM {α} [Repr α] : ArgF α → OfAstM (Ann Decimal α)
| .decimal ann val => pure { ann := ann, val := val }
| a => .throwExpected "scientific literal" a

def ofStrlitM {α} [Repr α] : ArgF α → OfAstM (Ann String α)
| .strlit ann val => pure { ann := ann, val := val }
| a => .throwExpected "string literal" a

def ofBytesM {α} [Repr α] : ArgF α → OfAstM (Ann ByteArray α)
| .bytes ann val => pure { ann := ann, val := val }
| a => .throwExpected "byte array" a

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
Get the expression at index `lvl` in the arguments.

Note that in conversion, we will
-/
def atArg {Ann α β} [SizeOf α] {e : α} (as : SizeBounded (Array (ArgF Ann)) e 1) (lvl : Nat)
        (act : (s : SizeBounded (ArgF Ann) e (-1)) → OfAstM β)
        (lvlP : lvl < as.val.size := by get_elem_tactic) :
        OfAstM β :=
  have lvlP : lvl < as.val.size := by omega
  have p : sizeOf as.val[lvl] ≤ sizeOf e + (-1 : Int) := by
      have asP := as.property
      have inP : as.val[lvl] ∈ as.val := by simp
      have eltSizeOfP := Array.sizeOf_lt_of_mem_strict inP;
      omega
  act ⟨as.val[lvl], p⟩

/--
Get the expression at index `lvl` in the arguments.

Note that in conversion, we will
-/
def exprEtaArg{Ann α T} [Repr Ann] [HasEta α T] {e : Expr} {n : Nat} (as : SizeBounded (Array (ArgF Ann)) e 1) (_ : as.val.size ≤ n) (lvl : Nat)
        (act : (s : ExprF Ann) → sizeOf s < sizeOf e → OfAstM α) :
        OfAstM α :=
  if lvlP : lvl < as.val.size then
    let i := as.val.size - 1 - lvl
    have iP : i < as.val.size := by omega
    match arg_eq : as.val[i] with
    | .expr a1 => act a1 (by
        have asP := as.property
        have idxP := Array.sizeOf_getElem as.val i iP;
        simp +arith [arg_eq] at idxP;
        omega)
    | _ => .throwExpectedExpr as.val[i]
  else
    let i := n - 1 - lvl
    return HasEta.bvar i

end Strata.OfAstM
end
