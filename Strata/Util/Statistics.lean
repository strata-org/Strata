/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashMap.Basic
import Lean.Exception
public meta import Lean.Elab.Command

/-! # Transform statistics

A lightweight map from string keys to integer counters, used by program
transformations to record how much work they performed.
-/

public section

/-- A map from statistic keys to integer counters. -/
structure Statistics where
  data : Std.HashMap String Int := {}
  deriving Inhabited

namespace Statistics

/-- Increment a counter by `n` (default 1), initializing to `n` if absent. -/
def increment (stats : Statistics) (key : String) (n : Nat := 1) : Statistics :=
  if n == 0 then stats
  else { data := stats.data.alter key (fun
    | some v => some (v + (n : Int))
    | none   => some (n : Int)) }

/-- Merge two statistics maps by summing values for shared keys. -/
def merge (s1 s2 : Statistics) : Statistics :=
  { data := s2.data.fold (fun acc k v => acc.alter k (fun
    | some v' => some (v' + v)
    | none    => some v)) s1.data }

/-- Format all statistics as `[statistics] key: value` lines, sorted by key. -/
def format (stats : Statistics) : String :=
  let entries := stats.data.fold (fun acc k v => (k, v) :: acc) []
  let sorted := entries.toArray.qsort (fun a b => a.fst < b.fst)
  let lines := sorted.map fun (k, v) => s!"[statistics] {k}: {v}"
  "\n".intercalate lines.toList

/-- Look up a counter value, returning 0 if absent. -/
def get (stats : Statistics) (key : String) : Int :=
  stats.data.getD key 0

end Statistics

/-! ## Derive `ToString` for enum-like stat key inductives

`#derive_prefixed_toString Ty "Prefix"` generates:

```
instance : ToString Ty where
  toString
    | .ctor₁ => "Prefix.ctor₁"
    | .ctor₂ => "Prefix.ctor₂"
```
-/

open Lean Elab Command Parser in
/-- Generate a `ToString` instance for an enum-like inductive type where each
    constructor `.foo` is rendered as `"Prefix.foo"`. -/
elab "#derive_prefixed_toString " ty:ident pfx:str : command => do
  let tyName ← resolveGlobalConstNoOverload ty
  let some (.inductInfo val) := (← getEnv).find? tyName
    | throwError m!"'{tyName}' is not an inductive type"
  let pfxStr := pfx.getString
  let arms := val.ctors.map fun ctorName =>
    match ctorName with
    | .str _ shortName => s!"    | .{shortName} => \"{pfxStr}.{shortName}\""
    | _ => dbg_trace "unexpected ctor name: {ctorName}"; "<unknown>"
  let armsStr := "\n".intercalate arms
  let code := s!"instance : ToString {ty.getId} where\n  toString\n{armsStr}"
  let env ← getEnv
  let stx ← IO.ofExcept (runParserCategory env `command code)
  elabCommand stx

end
