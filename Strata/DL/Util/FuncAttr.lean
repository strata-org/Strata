/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
/-!
## Structured Function Attributes

Structured attributes for controlling partial evaluator behavior
(inlining, concrete evaluation).
-/

namespace Strata.DL.Util

/-- Attributes for functions that control partial evaluator behavior. -/
inductive FuncAttr where
  /-- Always inline the function body when called. -/
  | inline
  /-- Inline when argument at `paramIdx` is a constructor application. -/
  | inlineIfConstr (paramIdx : Nat)
  /-- Use concrete evaluation when argument at `paramIdx` is a constructor application. -/
  | evalIfConstr (paramIdx : Nat)
  /-- Use concrete evaluation when argument at `paramIdx` is a canonical value. -/
  | evalIfCanonical (paramIdx : Nat)
  /-- Inline the function body when all arguments are canonical values.
      Used for int-recursive functions (without `@[cases]`) so that concrete
      evaluation can unfold calls like `factorial(5)` at partial-evaluation time. -/
  | inlineIfAllCanonical
  deriving DecidableEq, Repr, Inhabited, BEq

open Std (ToFormat Format format)

instance : ToFormat FuncAttr where
  format
    | .inline => "inline"
    | .inlineIfConstr i => f!"inlineIfConstr {i}"
    | .evalIfConstr i => f!"evalIfConstr {i}"
    | .evalIfCanonical i => f!"evalIfCanonical {i}"
    | .inlineIfAllCanonical => "inlineIfAllCanonical"

instance : ToFormat (Array FuncAttr) where
  format attrs := Format.joinSep (attrs.toList.map format) ", "

/-- Return the `paramIdx` of the first `inlineIfConstr` attribute, if any. -/
def FuncAttr.findInlineIfConstr (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .inlineIfConstr i => some i | _ => none

/-- Return the `paramIdx` of the first `evalIfConstr` attribute, if any. -/
def FuncAttr.findEvalIfConstr (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .evalIfConstr i => some i | _ => none

/-- Return the `paramIdx` of the first `evalIfCanonical` attribute, if any. -/
def FuncAttr.findEvalIfCanonical (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .evalIfCanonical i => some i | _ => none

/-- Return `true` if the attributes contain `inlineIfAllCanonical`.
    When true and all call arguments are canonical, the partial evaluator
    inlines the function body to enable concrete evaluation of int-recursive
    functions. -/
def FuncAttr.hasInlineIfAllCanonical (attrs : Array FuncAttr) : Bool :=
  attrs.any (· == .inlineIfAllCanonical)

end Strata.DL.Util
end
