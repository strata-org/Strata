/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataCortex.Implementation.Interpret

/-! # Builders for the Cortex interpreter's tests on wire programs -/

open Strata Cortex.Wire

namespace Cortex.TestCortex

public section

/-- A range with no file, which the wire reader gives no source location. -/
def noLoc : FileRange := { file := .file "", range := { start := ⟨0⟩, stop := ⟨0⟩ } }

def blk (label : String) (cmds : List Cmd) (t : Transfer) : Block := { label, cmds, transfer := t }

/-- A procedure without inputs or outputs at `source`, whose one block runs `cmds`: an entry unless `entry := false`. -/
def proc (name : String) (source : FileRange) (cmds : List Cmd) (entry := true) : Wire.Procedure :=
  { name, inputs := [], outputs := [], throws := none, requires := [], entry, source,
    body := some { entry := "b0", handlers := [], blocks := [blk "b0" cmds (.finish source)] } }

/-- The range of byte `n` of `T.java`; the tests print it as `n`. -/
def at_ (n : Nat) : FileRange := { file := .file "T.java", range := { start := ⟨n⟩, stop := ⟨n + 1⟩ } }

/-- An entry procedure at `at_ n` whose one block runs `cmds`. -/
def entry (name : String) (n : Nat) (cmds : List Cmd) : Wire.Procedure := proc name (at_ n) cmds

end

end Cortex.TestCortex
