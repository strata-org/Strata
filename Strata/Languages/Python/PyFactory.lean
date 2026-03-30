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
causes `pythonRegexToCore` to be called twice via `concreteEval`:

1. **`re_pattern_error(pattern)`** — Parses the pattern and returns
   `NoError()` on success or `RePatternError(msg)` for a genuinely malformed
   pattern.  Unimplemented features return `NoError()` because Python would
   succeed at runtime; the mode-specific factory staying uninterpreted provides
   a sound over-approximation for those cases.  The prelude checks this first
   and returns `exception(err)` for pattern errors, modeling Python's
   `re.error`.

2. **`re_fullmatch_str(pattern)`** (or `re_match_str`/`re_search_str`) —
   Compiles the pattern with the correct `MatchMode`.  Returns the compiled
   regex on success, or `.none` on error (leaving the function uninterpreted).
   Since pattern errors are already caught by `re_pattern_error`, the `.none`
   case here only fires for unimplemented features, producing `unknown` VCs —
   a sound over-approximation.

The double parse is defensible because `pythonRegexToCore` is fast enough -- it
runs at translation time, not solver time, and keeps the factory functions
orthogonal.
-/

open Core
open Lambda LTy.Syntax LExpr.SyntaxMono

-- Mode-specific regex compilation.  Each function compiles a Python regex
-- string with the correct MatchMode so that anchors (^/$) are handled
-- properly.
private def mkModeCompileFunc (name : String) (mode : MatchMode) :
    LFunc Core.CoreLParams :=
    { name := name,
      typeArgs := [],
      inputs := [("pattern", mty[string])],
      output := mty[regex],
      concreteEval := some
        (fun _ args => match args with
          | [LExpr.strConst () s] =>
            let (expr, maybe_err) := pythonRegexToCore s mode
            match maybe_err with
            | none => .some expr
            | some _ => .none
          | _ => .none)
      }

def reFullmatchStrFunc : LFunc Core.CoreLParams :=
  mkModeCompileFunc "re_fullmatch_str" .fullmatch
def reMatchStrFunc     : LFunc Core.CoreLParams :=
  mkModeCompileFunc "re_match_str"     .match
def reSearchStrFunc    : LFunc Core.CoreLParams :=
  mkModeCompileFunc "re_search_str"    .search

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
      reFullmatchStrFunc,
      reMatchStrFunc,
      reSearchStrFunc,
      rePatternErrorFunc
    ]

/-- Core.Factory extended with regex factory functions. -/
def PythonFactory : @Lambda.Factory Core.CoreLParams :=
    Core.Factory.append ReFactory

end -- public section

-------------------------------------------------------------------------------
