/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Unit tests for `filterPrelude`'s seed handling (`extraSeeds` + `opSeed`).

`filterPrelude` restricts a prelude `Program` to only the declarations
transitively reachable from the names a user program references. Two seeding
knobs widen that reachable set:

- `opSeed : Operation → Option String` — for a primitive operator present in
  the user program, names the prelude function a frontend's elaboration would
  insert for it. That name is then retained as if the user had called it.
- `extraSeeds : List String` — names retained unconditionally, regardless of
  whether the user program references them.

These tests drive `filterPrelude` directly: a small prelude with three
functions, and user programs that do / do not contain an operator, confirming
exactly which prelude functions survive filtering.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.FilterPrelude

open Strata
open Strata.Laurel
open StrataTest.Util

namespace StrataTest.Util.FilterPreludeTest

/-- A prelude with three static procedures:
    - `op_add`   : the function an `Add` operator would elaborate to (opSeed target)
    - `unused_fn`: referenced by nothing (must be dropped unless seeded)
    - `always_kept`: the unconditional `extraSeeds` target -/
def preludeProgram : IO Laurel.Program := translateLaurel <|
#strata
program Laurel;
function op_add(x: int, y: int): int { x };
function unused_fn(x: int): int { x };
function always_kept(x: int): int { x };
#end

/-- `opSeed` mapping `Add ↦ "op_add"`; every other operator is unseeded. -/
def addOpSeed : Operation → Option String
  | .Add => some "op_add"
  | _ => none

/-- Run `filterPrelude` and report the sorted names of the retained prelude
    static procedures (or the error). -/
def retainedNames (user : Laurel.Program) : IO Unit := do
  let prelude ← preludeProgram
  match filterPrelude prelude user (extraSeeds := ["always_kept"]) (opSeed := addOpSeed) with
  | .error e => IO.println s!"error: {e}"
  | .ok filtered =>
    let names := filtered.staticProcedures.map (·.name.text)
    IO.println (toString (names.mergeSort (· ≤ ·)))

/-! ## (a) opSeed path: operator present ⇒ its prelude function is retained

The user program uses `+` (a `PrimitiveOp Add`). `opSeed` maps `Add` to
`op_add`, so `op_add` is seeded and survives filtering. `always_kept` survives
via `extraSeeds`. `unused_fn` is referenced by nothing and is dropped. -/

/-- info: [always_kept, op_add] -/
#guard_msgs in
#eval! do
  let user ← translateLaurel <|
#strata
program Laurel;
function useAdd(x: int, y: int): int { x + y };
#end
  retainedNames user

/-! ## (b) no operator ⇒ opSeed function dropped; extraSeeds still retained

The user program contains no `Add` operator, so `op_add` is not seeded and is
dropped. `always_kept` is retained unconditionally via `extraSeeds`, and
`unused_fn` is dropped. This pins that `extraSeeds` retention is unconditional
while `opSeed` retention is gated on the operator actually appearing. -/

/-- info: [always_kept] -/
#guard_msgs in
#eval! do
  let user ← translateLaurel <|
#strata
program Laurel;
function noOp(x: int): int { x };
#end
  retainedNames user

end StrataTest.Util.FilterPreludeTest
