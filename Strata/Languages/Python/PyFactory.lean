/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Verifier
public import Strata.Languages.Python.Regex.ReToCore

namespace Strata
namespace Python

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
      concreteEval := some
        (fun _ args => match args with
          | [LExpr.strConst () pattern, sExpr] =>
            let (regexExpr, maybe_err) := pythonRegexToCore pattern mode
            match maybe_err with
            | none => .some (LExpr.mkApp () (.op () "Str.InRegEx" (some mty[string → (regex → bool)])) [sExpr, regexExpr])
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
      concreteEval := some
        (fun _ args => match args with
          | [LExpr.strConst () s] =>
            let (_, maybe_err) := pythonRegexToCore s .fullmatch -- mode irrelevant: errors come from parseTop before mode-specific compilation
            match maybe_err with
            | none =>
              .some (LExpr.mkApp () (.op () "NoError" (some mty[Error])) [])
            | some (ParseError.unimplemented ..) =>
              .some (LExpr.mkApp () (.op () "NoError" (some mty[Error])) [])
            | some (ParseError.patternError msg ..) =>
              .some (LExpr.mkApp () (.op () "RePatternError" (some mty[string → Error]))
                  [.strConst () (toString msg)])
          | _ => .none)
      }

def ReFactory : @Factory Core.CoreLParams :=
    #[
      reFullmatchBoolFunc,
      reMatchBoolFunc,
      reSearchBoolFunc,
      rePatternErrorFunc
    ]

/-- Core.Factory extended with regex factory functions. -/
def PythonFactory : @Lambda.Factory Core.CoreLParams :=
    Core.Factory.append ReFactory

end -- public section

-------------------------------------------------------------------------------
