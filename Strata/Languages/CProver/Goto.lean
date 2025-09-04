/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.CProver.Expr

namespace GotoIR
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

/--
GOTO instruction type; corresponds to `goto_program_instruction_typet`.
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

def Target := Nat
deriving Repr, Inhabited, DecidableEq

instance {n} : OfNat Target n := ⟨n⟩
def Target.toNat (t : Target) : Nat := t

/--
GOTO instruction, corresponds to `instructiont`.
-/
structure Instruction where
  instrType   : InstructionType := .NO_INSTRUCTION_TYPE
  guard       : Expr            := true_expr
  targets     : List Target     := []
  code        : Option Expr     := .none
  /--
  A globally unique number to identify a program location.
  It's guaranteed to be ordered in program order within
  one goto program.
  -/
  locationNum : Nat             := 0
  /--
  A number to identify branch targets. This is used to assign each target a
  unique index.
  -/
  targetNum   : Nat             := 0
  deriving Repr, Inhabited

structure Program where
  instructions : Array Instruction
  deriving Repr, Inhabited

instance : ToFormat Instruction where
  format i :=
    let itype := f!"{repr i.instrType}"
    let guard := if Expr.BEq i.guard true_expr then f!"" else f!"GUARD: {i.guard}"
    let targets := if i.targets.isEmpty then f!"" else f!"TARGETS: {repr i.targets}"
    f!"{i.locationNum}: {itype} {i.code} {guard} {targets}"

-------------------------------------------------------------------------------

section Examples

private def i_expr : Expr :=
  {
    id := .symbol "i",
    type := .BitVector (.UnsignedBV 32)
  }

-- DECL i : unsignedbv[32]
private def i_decl : Instruction :=
  { instrType := .DECL,
    guard := { id := .constant "true", type := .Boolean },
    targets := [],
    code := some ({ id := .code .Decl,
                    type := .BitVector (.UnsignedBV 32),
                    operands := [i_expr] }),
    locationNum := 0,
    targetNum := 0
   }

end Examples

-------------------------------------------------------------------------------
end GotoIR
