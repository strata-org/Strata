/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Verifier
public import Strata.Languages.Python.Regex.ReToCore

namespace Strata
namespace Python

-- nosourcerange-file: expressions synthesized by the Python factory (regex patterns, error
-- constructors) are generated programmatically, not parsed from source.

public section

-------------------------------------------------------------------------------

/-
## Python regex verification — factory functions

These factory functions provide `concreteEval` implementations that call
`pythonRegexToCore` to translate Python regex pattern strings into SMT-LIB
regex expressions at verification time.

### Architecture

Python's `re.compile` is a semantic no-op in the Laurel pipeline — it returns
the pattern string unchanged.  The actual compilation to SMT-LIB regex happens
at the point of matching (`re.fullmatch`, `re.match`, `re.search`), where the
match mode is known.

This is important because `pythonRegexToCore` produces *different* regex
expressions depending on the mode -- in particular, it handles anchors (`^`/`$`)
by generating a union of anchor-activation variants with appropriate `.*`
wrapping (see `ReToCore.lean`).  Compiling once at `re.compile` time would
require knowing the eventual match mode, which is not available.

### Factory functions

Each call to `re.fullmatch(pattern, s)` (and similarly `re.match`/`re.search`)
causes `pythonRegexToCore` to be called (at most) twice via `concreteEval`:

1. **`re_pattern_error(pattern)`** — Parses the pattern and returns
   `NoError()` on success or `RePatternError(msg)` for a genuinely malformed
   pattern.  Unimplemented features return `NoError()` because Python would
   succeed at runtime; the mode-specific factory staying uninterpreted provides
   a sound over-approximation for those cases.  The prelude checks this first
   and returns `exception(err)` for pattern errors, modeling Python's
   `re.error`.

2. **`re_fullmatch_bool(pattern, s)`** (or `re_match_bool`/`re_search_bool`) —
   Compiles the pattern with the correct `MatchMode` and returns
   `Str.InRegEx(s, compiled_regex)` on success, or `.none` on failure (leaving
   the function uninterpreted as a `Bool` UF).  Since pattern errors are already
   caught by `re_pattern_error`, the `.none` case here only fires for
   unimplemented features (e.g. `\S`, `\d`), producing `unknown` VCs — a sound
   over-approximation.

   Critically, an uninterpreted `Bool` UF does not cause SMT theory-combination
   errors.  The previous design used `re_*_str` (returning `RegLan`) as the
   uninterpreted fallback, but cvc5 rejects uninterpreted `RegLan` UFs with
   "Regular expression terms are not supported in theory combination".

The double parse is defensible because `pythonRegexToCore` is fast enough -- it
runs at translation time, not solver time, and keeps the factory functions
orthogonal.

-/

open Core
open Lambda LTy.Syntax LExpr.SyntaxMono

-- Bool-valued factory.  See architecture comment above.
private def mkModeBoolFunc (name : String) (mode : MatchMode) :
    LFunc Core.CoreLParams :=
    { name := name,
      typeArgs := [],
      inputs := [("pattern", mty[string]), ("s", mty[string])],
      output := mty[bool],
      attr := #[.evalIfCanonical 0],
      concreteEval := some
        (fun _ args => match args with
          | [LExpr.strConst _ pattern, sExpr] =>
            let (regexExpr, maybe_err) := pythonRegexToCore pattern mode
            match maybe_err with
            | none => .some (LExpr.mkApp ExprSourceLoc.none (.op ExprSourceLoc.none "Str.InRegEx" (some mty[string → (regex → bool)])) [sExpr, regexExpr])
            | some _ => .none
          | _ => .none)
      }

def reFullmatchBoolFunc : LFunc Core.CoreLParams :=
  mkModeBoolFunc "re_fullmatch_bool" .fullmatch
def reMatchBoolFunc     : LFunc Core.CoreLParams :=
  mkModeBoolFunc "re_match_bool"     .match
def reSearchBoolFunc    : LFunc Core.CoreLParams :=
  mkModeBoolFunc "re_search_bool"    .search

def rePatternErrorFunc : LFunc Core.CoreLParams :=
    { name := "re_pattern_error",
      typeArgs := [],
      inputs := [("pattern", mty[string])],
      output := mty[Error],
      attr := #[.evalIfCanonical 0],
      concreteEval := some
        (fun _ args => match args with
          | [LExpr.strConst _ s] =>
            let (_, maybe_err) := pythonRegexToCore s .fullmatch -- mode irrelevant: errors come from parseTop before mode-specific compilation
            match maybe_err with
            | none =>
              .some (LExpr.mkApp ExprSourceLoc.none (.op ExprSourceLoc.none "NoError" (some mty[Error])) [])
            | some (ParseError.unimplemented ..) =>
              .some (LExpr.mkApp ExprSourceLoc.none (.op ExprSourceLoc.none "NoError" (some mty[Error])) [])
            | some (ParseError.patternError msg ..) =>
              .some (LExpr.mkApp ExprSourceLoc.none (.op ExprSourceLoc.none "RePatternError" (some mty[string → Error]))
                  [.strConst ExprSourceLoc.none (toString msg)])
          | _ => .none)
      }

-- Integer exponentiation with constant folding via concreteEval.
-- Forward-declared before CoreOnlyDelimiter in PythonLaurelCorePrelude so
-- PPow can reference it. The factory provides the concreteEval implementation.
def intPowFunc : LFunc Core.CoreLParams :=
    { name := "int_pow",
      typeArgs := [],
      inputs := [("base", mty[int]), ("exp", mty[int])],
      output := mty[int],
      concreteEval := some
        (fun md args => match args with
          | [b, e] => match LExpr.denoteInt b, LExpr.denoteInt e with
            | some bv, some ev =>
              if ev ≥ 0 then .some (LExpr.intConst md (bv ^ ev.toNat)) else .none
            | _, _ => .none
          | _ => .none)
      }

-- Float exponentiation (uninterpreted). Used for negative integer exponents
-- where Python returns a float (e.g. 2 ** -3 = 0.125).
-- This function should NOT be mapped to any real-based power functions in solvers, since float power is imprecise.
def floatPowFunc : LFunc Core.CoreLParams :=
    { name := "float_pow",
      typeArgs := [],
      inputs := [("base", mty[real]), ("exp", mty[real])],
      output := mty[real]
      }

-- Integer right shift with constant folding via concreteEval.
-- Computes floor(x / 2^n) for n ≥ 0, avoiding Int.SafeDiv preconditions.
def intRshiftFunc : LFunc Core.CoreLParams :=
    { name := "int_rshift",
      typeArgs := [],
      inputs := [("x", mty[int]), ("n", mty[int])],
      output := mty[int],
      concreteEval := some
        (fun md args => match args with
          | [x, n] => match LExpr.denoteInt x, LExpr.denoteInt n with
            | some xv, some nv =>
              if nv ≥ 0 then .some (LExpr.intConst md (xv / (2 ^ nv.toNat))) else .none
            | _, _ => .none
          | _ => .none)
      }

def ReFactory : Factory Core.CoreLParams := .ofArray
    #[
      reFullmatchBoolFunc,
      reMatchBoolFunc,
      reSearchBoolFunc,
      rePatternErrorFunc,
      intPowFunc,
      floatPowFunc,
      intRshiftFunc
    ]

/-- Core.Factory extended with regex factory functions. -/
def PythonFactory : @Lambda.Factory Core.CoreLParams :=
    Core.Factory.append ReFactory.toArray

end -- public section

-------------------------------------------------------------------------------
