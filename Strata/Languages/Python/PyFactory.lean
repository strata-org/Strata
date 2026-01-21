/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Python.Regex.ReToCore

namespace Strata
namespace Python

-------------------------------------------------------------------------------

/-
Candidate translation pass for Python `re` code:

## Python Code:

```
...
PATTERN = r"^[a-z0-9][a-z0-9.-]{1,3}[a-z0-9]$"
REGEX = re.compile(PATTERN) # default flags == 0
...
if not re.match(REGEX, name) then # default flags == 0
  return False
...
```

## Corresponding Strata.Core:

```
procedure _main () {

var PATTERN : string = "^[a-z0-9][a-z0-9.-]{1,3}[a-z0-9]$";

var REGEX : regex;
var $__REGEX : Except Error regex := PyReCompile(PATTERN, 0)

if ExceptErrorRegex_isOK($__REGEX) then {
  REGEX := ExceptErrorRegex_getOK($__REGEX);
} else if (Error_isUnimplemented(ExceptErrorRegex_getError($__REGEX)) then {
  // Unsupported by Strata.
  havoc REGEX;
} else {
  //
  // TODO: Implement a version of `assert` that takes an expression to be
  // evaluated when the assertion fails. In this case, we'd display the
  // (computed) error message in `ExceptErrorRegex_getError($__REGEX)`.
  //
  // E.g., `assert false (printOnFailure := ExceptErrorRegex_getError($__REGEX));`
  //
  assert false;
}
...

if not PyReMatch(REGEX, name, 0) then
  return false
}
```

-/

open Core
open Lambda LTy.Syntax LExpr.SyntaxMono

def reCompileFunc : LFunc Core.CoreLParams :=
    { name := "PyReCompile",
      typeArgs := [],
      inputs := [("string", mty[string]),
                 ("flags", mty[int])]
      output := mty[ExceptErrorRegex],
      concreteEval := some
        (fun _ args => match args with
          | [LExpr.strConst () s, LExpr.intConst () 0] =>
            -- This function has a concrete evaluation implementation only when
            -- flags == 0.
            -- (FIXME): We use `.match` mode below because we support only
            -- `re.match` for now. However, `re.compile` isn't mode-specific in
            -- general.
            let (expr, maybe_err) := pythonRegexToCore s .match
            match maybe_err with
            | none =>
              -- Note: Do not use `eb` (in Strata Core Syntax) here (e.g., see below)
              -- eb[(~ExceptErrorRegex_mkOK expr)]
              -- that captures `expr` as an `.fvar`.
              .some (LExpr.mkApp () (.op () "ExceptErrorRegex_mkOK" none) [expr])
            | some (ParseError.unimplemented msg _pattern _pos) =>
              .some (LExpr.mkApp () (.op () "ExceptErrorRegex_mkErr" none)
                  [LExpr.mkApp () (.op () "Error_Unimplemented" none) [.strConst () (toString msg)]])
            | some (ParseError.patternError msg _pattern _pos) =>
              .some (LExpr.mkApp () (.op () "ExceptErrorRegex_mkErr" none)
                  [LExpr.mkApp () (.op () "Error_RePatternErr" none) [.strConst () (toString msg)]])
          | _ => .none)
      }

def ReFactory : @Factory Core.CoreLParams :=
    #[
      reCompileFunc
    ]

-------------------------------------------------------------------------------
