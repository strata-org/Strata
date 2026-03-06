/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

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
  deriving DecidableEq, Repr, Inhabited, BEq

open Std (ToFormat Format format)

instance : ToFormat FuncAttr where
  format
    | .inline => "inline"
    | .inlineIfConstr i => f!"inlineIfConstr {i}"
    | .evalIfConstr i => f!"evalIfConstr {i}"

instance : ToFormat (Array FuncAttr) where
  format attrs := Format.joinSep (attrs.toList.map format) ", "

/-- Return the `paramIdx` of the first `inlineIfConstr` attribute, if any. -/
def FuncAttr.findInlineIfConstr (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .inlineIfConstr i => some i | _ => none

/-- Return the `paramIdx` of the first `evalIfConstr` attribute, if any. -/
def FuncAttr.findEvalIfConstr (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .evalIfConstr i => some i | _ => none

end Strata.DL.Util
