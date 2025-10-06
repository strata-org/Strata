/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Expr
import Strata.Backends.CBMC.GOTO.Code

namespace CProverGOTO
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

/--
GOTO instruction type; corresponds to
[`goto_program_instruction_typet`](https://diffblue.github.io/cbmc/goto__program_8h.html#a9e03d66cd12c59d9d3daad1ec6296beb).
-/
inductive InstructionType where
  | NO_INSTRUCTION_TYPE
  | GOTO             -- branch, possibly guarded
  | ASSUME           -- non-failing guarded self loop
  | ASSERT           -- assertions
  | OTHER            -- anything else
  | SKIP             -- just advance the PC
  | START_THREAD     -- spawns an asynchronous thread
  | END_THREAD       -- end the current thread
  | LOCATION         -- semantically like SKIP
  | END_FUNCTION     -- exit point of a function
  | ATOMIC_BEGIN     -- marks a block without interleavings
  | ATOMIC_END       -- end of a block without interleavings
  | SET_RETURN_VALUE -- set function return value (no control-flow change)
  | ASSIGN           -- assignment lhs:=rhs
  | DECL             -- declare a local variable
  | DEAD             -- marks the end-of-live of a local variable
  | FUNCTION_CALL    -- call a function
  | THROW            -- throw an exception
  | CATCH            -- push, pop or enter an exception handler
  | INCOMPLETE_GOTO  -- goto where target is yet to be determined
  deriving Repr, Inhabited, DecidableEq

instance : ToString InstructionType where
  toString
  | InstructionType.NO_INSTRUCTION_TYPE => "NO_INSTRUCTION_TYPE"
  | InstructionType.GOTO => "GOTO"
  | InstructionType.ASSUME => "ASSUME"
  | InstructionType.ASSERT => "ASSERT"
  | InstructionType.OTHER => "OTHER"
  | InstructionType.SKIP => "SKIP"
  | InstructionType.START_THREAD => "START_THREAD"
  | InstructionType.END_THREAD => "END_THREAD"
  | InstructionType.LOCATION => "LOCATION"
  | InstructionType.END_FUNCTION => "END_FUNCTION"
  | InstructionType.ATOMIC_BEGIN => "ATOMIC_BEGIN"
  | InstructionType.ATOMIC_END => "ATOMIC_END"
  | InstructionType.SET_RETURN_VALUE => "SET_RETURN_VALUE"
  | InstructionType.ASSIGN => "ASSIGN"
  | InstructionType.DECL => "DECL"
  | InstructionType.DEAD => "DEAD"
  | InstructionType.FUNCTION_CALL => "FUNCTION_CALL"
  | InstructionType.THROW => "THROW"
  | InstructionType.CATCH => "CATCH"
  | InstructionType.INCOMPLETE_GOTO => "INCOMPLETE_GOTO"

-------------------------------------------------------------------------------

def Target := Nat
deriving Repr, Inhabited, DecidableEq

instance {n} : OfNat Target n := ⟨n⟩
def Target.toNat (t : Target) : Nat := t

instance : ToString Target where
  toString t := toString $ repr t

-------------------------------------------------------------------------------

/--
GOTO instruction, corresponds to
[`instructiont`](https://diffblue.github.io/cbmc/classgoto__programt_1_1instructiont.html).
-/
structure Instruction where
  type        : InstructionType := .NO_INSTRUCTION_TYPE
  -- (FIXME) Many instructions ignore the `guard` field. Should we consider making
  -- `guard` an `Option Expr` instead?
  guard       : Expr            := .true
  -- (FIXME) Many instructions ignore the `code` field. Should we consider
  -- making `code` an `Option Code` instead?
  -- (FIXME) Maybe `guard` and `code` usage is really an XOR?
  code        : Code            := Code.skip
  /--
  Invariant: A target should only contain a known `locationNum` within the same
  procedure.
  -/
  target      : Option Target   := .none
  sourceLoc   : SourceLocation  := .nil
  /--
  A globally unique number to identify a program location.
  It's guaranteed to be ordered in program order within
  one goto program (a single procedure).
  -/
  locationNum : Target             := 0
  /--
  Corresponds to `labelst`.
  Use within CProver: users can specify which loop to unwind using these labels.
  For now, think of these as a set of labels instead of a list.
  (FIXME) Maybe put `labels` in `sourceLoc`? It doesn't affect the semantics, so
  feels like it should belong in the metadata.
  -/
  labels : List String := []
  deriving Repr, Inhabited

instance : ToString Instruction where
  toString instr :=
    let code_str := f!" {instr.code}"
    let guard_str := if Expr.beq instr.guard Expr.true then "" else s!" [{Std.format instr.guard}]"
    s!"{instr.type}{code_str}{guard_str}"

-------------------------------------------------------------------------------
