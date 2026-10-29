/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.NameMangling
import all Strata.Languages.Core.NameMangling

/-! # Round-trip sanity checks for `Core.NameMangling`

Elaboration-time `#guard` cases that exercise the mangler and demangler on
representative inputs.  Each check evaluates through Lean's interpreter; a
regression in either the mangling scheme or the demangler surfaces here as
a build failure.

The mangling scheme lives in `Strata/Languages/Core/NameMangling.lean`. -/

namespace Core.NameMangling

open Strata.PtrCache

-- Nullary mangling: no type args, no mangling — the base name is returned
-- unchanged.  The demangler correctly rejects such a name as "not mangled"
-- (`none`), which is the same outcome as calling it on any raw identifier.
#guard (mangleFuncName PtrCache.empty "id" []).1.name == "id"
#guard demangleFuncName "id" == none
#guard demangleFuncName (mangleFuncName PtrCache.empty "id" []).1.name == none

-- Single-arg round-trip.
#guard (mangleFuncName PtrCache.empty "id" [Lambda.LMonoTy.int]).1.name == "$__mono#id#int"
#guard demangleFuncName "$__mono#id#int" == some ("id", "int")
#guard demangleFuncName (mangleFuncName PtrCache.empty "id" [Lambda.LMonoTy.int]).1.name ==
       some ("id", "int")

-- Two-arg round-trip.  Top-level arg lists are `#`-joined, and the demangler
-- recovers the whole typemangle by splitting on the first `#` after the prefix.
#guard (mangleFuncName PtrCache.empty "select"
         [Lambda.LMonoTy.int, Lambda.LMonoTy.int]).1.name == "$__mono#select#int#int"
#guard demangleFuncName
         (mangleFuncName PtrCache.empty "select"
            [Lambda.LMonoTy.int, Lambda.LMonoTy.int]).1.name ==
       some ("select", "int#int")

-- User-datatype arg: `Sequence<int>` mangles to `Sequence#1#int` — arg count
-- and args separated by `#`.
#guard demangleFuncName
         (mangleFuncName PtrCache.empty "Sequence.length"
            [.tcons "Sequence" [Lambda.LMonoTy.int]]).1.name ==
       some ("Sequence.length", "Sequence#1#int")

-- The mangled string spells out each `tcons`'s arity, so the head's arg count
-- is visible without re-parsing.  In a well-formed program a datatype's arity
-- is fixed at declaration, so `Pair<int, int>` is the only reachable form;
-- the prefix is documentary rather than disambiguating.
#guard (mangleFuncName PtrCache.empty "f"
         [.tcons "Pair" [Lambda.LMonoTy.int, Lambda.LMonoTy.int]]).1.name ==
       "$__mono#f#Pair#2#int#int"

-- Nested `tcons`: `Map<Sequence<int>, bool>` exercises the mutual recursion
-- between `mangleTy` and `mangleTyArgs`.  Each `tcons` layer contributes its
-- `<name>#<arity>#<args…>` shape, so the inner `Sequence<int>` nests inside the
-- outer `Map`'s arg list.
#guard (mangleFuncName PtrCache.empty "lookup"
         [.tcons "Map" [.tcons "Sequence" [Lambda.LMonoTy.int], .tcons "bool" []]]).1.name ==
       "$__mono#lookup#Map#2#Sequence#1#int#bool"
#guard demangleFuncName
         (mangleFuncName PtrCache.empty "lookup"
            [.tcons "Map" [.tcons "Sequence" [Lambda.LMonoTy.int], .tcons "bool" []]]).1.name ==
       some ("lookup", "Map#2#Sequence#1#int#bool")

-- Bitvector types are mangled as `$bv#<n>`, not the bare `bv<n>`.  The `#`
-- delimiter is illegal in a user identifier, so a built-in `bv W8` (`.bitvec 8`
-- → `$bv#8`) can never collide with a user-declared nullary type spelled `bv8`
-- (`.tcons "bv8" []` → `bv8`); the two always get distinct mangled names.
#guard mangleTy (.bitvec 8) == "$bv#8"
#guard mangleTy (.tcons "bv8" []) == "bv8"
#guard mangleTy (.bitvec 8) != mangleTy (.tcons "bv8" [])
-- `.ftvar` fallback: a (non-ground) type variable mangles to its raw name.
#guard mangleTy (.ftvar "myVar") == "myVar"
#guard (mangleFuncName PtrCache.empty "f" [Lambda.LMonoTy.bitvec 32]).1.name == "$__mono#f#$bv#32"
#guard demangleFuncName "$__mono#f#$bv#32" == some ("f", "$bv#32")
-- The same function specialized at the built-in `bv8` vs. at a user `bv8` type
-- get distinct mangled names.
#guard (mangleFuncName PtrCache.empty "f" [Lambda.LMonoTy.bitvec 8]).1.name !=
       (mangleFuncName PtrCache.empty "f" [.tcons "bv8" []]).1.name

-- Non-mangled names return `none`.
#guard demangleFuncName "select" == none
#guard demangleFuncName "MyList..adtRank" == none
-- Any user or leftover name that doesn't start with `$__mono#` is rejected.
#guard demangleFuncName "$__mono$id" == none
-- Boundary: the bare prefix (no base name) demangles to empty base/typemangle.
#guard demangleFuncName (monoPrefix ++ monoDelim) == some ("", "")

-- Every non-nullary mangled name starts with `monoPrefix ++ monoDelim`.
-- (The nullary case returns the base name unchanged and so doesn't carry the
-- prefix — see the "nullary mangling" cases above.)
#guard (mangleFuncName PtrCache.empty "id" [Lambda.LMonoTy.int]).1.name.startsWith
         (monoPrefix ++ monoDelim)
#guard (mangleFuncName PtrCache.empty "select"
         [Lambda.LMonoTy.int, Lambda.LMonoTy.int]).1.name.startsWith
         (monoPrefix ++ monoDelim)

end Core.NameMangling
