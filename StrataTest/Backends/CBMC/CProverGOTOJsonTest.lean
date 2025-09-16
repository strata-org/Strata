/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.InstToJson

-------------------------------------------------------------------------------

section Tests
namespace CProverGOTO
open Lean
open CProverJson

/--
GOTO Function for `__CPROVER_initialize`:

```
__CPROVER_initialize /* __CPROVER_initialize */
        // 21 no location
        // Labels: __CPROVER_HIDE
        SKIP
        // 22 file <built-in-additions> line 8
        ASSIGN __CPROVER_dead_object := NULL
        // 23 file <built-in-additions> line 7
        ASSIGN __CPROVER_deallocated := NULL
        // 24 file <built-in-additions> line 12
        ASSIGN __CPROVER_max_malloc_size := 36028797018963968
        // 25 file <built-in-additions> line 9
        ASSIGN __CPROVER_memory_leak := NULL
        // 26 file <built-in-additions> line 16
        ASSIGN __CPROVER_rounding_mode := 0
        // 27 no location
        END_FUNCTION
```
-/
def defaultCProverInitialize (locationNum : Nat) : Program := {
  instructions := #[
    -- SKIP
    { type := .SKIP, locationNum := locationNum },

    -- ASSIGN __CPROVER_dead_object := NULL
    { type := .ASSIGN, locationNum := locationNum + 1,
      code := Code.assign (Expr.symbol "__CPROVER_dead_object" (Ty.UnsignedBV 64)) (Expr.constant "NULL" (Ty.UnsignedBV 64)),
      sourceLoc := {function := "__CPROVER_initialize", line := 8, file := "<built-in-additions>", workingDir := ""}},

    -- ASSIGN __CPROVER_deallocated := NULL
    { type := .ASSIGN, locationNum := locationNum + 2,
      code := Code.assign (Expr.symbol "__CPROVER_deallocated" (Ty.UnsignedBV 64)) (Expr.constant "NULL" (Ty.UnsignedBV 64)),
      sourceLoc := {function := "__CPROVER_initialize", line := 7, file := "<built-in-additions>", workingDir := ""}},

    -- ASSIGN __CPROVER_max_malloc_size := 36028797018963968
    { type := .ASSIGN, locationNum := locationNum + 3,
      code := Code.assign (Expr.symbol "__CPROVER_max_malloc_size" (Ty.UnsignedBV 64)) (Expr.constant "36028797018963968" (Ty.UnsignedBV 64)),
      sourceLoc := {function := "__CPROVER_initialize", line := 12, file := "<built-in-additions>", workingDir := ""}},

    -- ASSIGN __CPROVER_memory_leak := NULL
    { type := .ASSIGN, locationNum := locationNum + 4,
      code := Code.assign (Expr.symbol "__CPROVER_memory_leak" (Ty.UnsignedBV 64)) (Expr.constant "NULL" (Ty.UnsignedBV 64)),
      sourceLoc := {function := "__CPROVER_initialize", line := 9, file := "<built-in-additions>", workingDir := ""}},

    -- ASSIGN __CPROVER_rounding_mode := 0
    { type := .ASSIGN, locationNum := locationNum + 5,
      code := Code.assign (Expr.symbol "__CPROVER_rounding_mode" (Ty.SignedBV 32)) (Expr.constant "0" (Ty.SignedBV 32)),
      sourceLoc := {function := "__CPROVER_initialize", line := 16, file := "<built-in-additions>", workingDir := ""}},

    -- END_FUNCTION
    { type := .END_FUNCTION, locationNum := locationNum + 6,
      sourceLoc := {function := "__CPROVER_initialize", line := 0, file := "", workingDir := ""}}
  ]
}

-------------------------------------------------------------------------------

/-
Generate an appropriate GOTO function for `__CPROVER_start`.
```
__CPROVER__start /* __CPROVER__start */
        // 8 no location
        // Labels: __CPROVER_HIDE
        SKIP
        // 9 file <built-in-additions> line 24
        CALL __CPROVER_initialize()
        // 10 file simpleAdd.c line 5 function simpleAdd
        DECL __CPROVER__start::x : signedbv[32]
        // 11 file simpleAdd.c line 5 function simpleAdd
        ASSIGN __CPROVER__start::x := side_effect statement="nondet" is_nondet_nullable="1"
        // 12 file simpleAdd.c line 5 function simpleAdd
        INPUT address_of("x"[0]) __CPROVER__start::x
        // 13 file simpleAdd.c line 5 function simpleAdd
        DECL __CPROVER__start::y : signedbv[32]
        // 14 file simpleAdd.c line 5 function simpleAdd
        ASSIGN __CPROVER__start::y := side_effect statement="nondet" is_nondet_nullable="1"
        // 15 file simpleAdd.c line 5 function simpleAdd
        INPUT address_of("y"[0]) __CPROVER__start::y
        // 16 file simpleAdd.c line 5
        CALL return' := simpleAdd(__CPROVER__start::x, __CPROVER__start::y)
        // 17 file simpleAdd.c line 5
        OUTPUT address_of("return'"[0])
        // 18 no location
        DEAD __CPROVER__start::y
        // 19 no location
        DEAD __CPROVER__start::x
        // 20 no location
        END_FUNCTION
```
-/
def genCProverStart (funcName : String) (args : List (String × Ty)) (locationNum : Nat) : Program :=
  let genFunArgForCProverStart (funcName : String) (argName : String) (argTy : Ty) (locationNum : Nat) : List Instruction :=
    [
      -- DECL __CPROVER__start::argName : argTy
      { type := .DECL, locationNum := locationNum,
        code := Code.decl (Expr.symbol s!"__CPROVER__start::{argName}" argTy),
        sourceLoc := {function := funcName, line := 5, file := s!"{funcName}.c", workingDir := ""}},
      -- ASSIGN __CPROVER__start::argName := side_effect
      { type := .ASSIGN, locationNum := locationNum + 1,
        code := Code.assign (Expr.symbol s!"__CPROVER__start::{argName}" argTy) (Expr.side_effect_nondet [("statement", Expr.constant "nondet" Ty.String), ("is_nondet_nullable", Expr.constant "1" Ty.String)]),
        sourceLoc := {function := funcName, line := 5, file := s!"{funcName}.c", workingDir := ""}},
      -- INPUT address_of(argName) __CPROVER__start::argName
      { type := .OTHER, locationNum := locationNum + 2,
        sourceLoc := {function := funcName, line := 5, file := s!"{funcName}.c", workingDir := ""}}
    ]
  let argInstructions := (args.mapIdx (fun i (argName, argTy) =>
      let baseIdx := locationNum + 2 + i * 3
      genFunArgForCProverStart funcName argName argTy baseIdx)).flatten
  let callIdx := locationNum + 2 + args.length * 3
  let deadInstructions := args.mapIdx fun i (argName, argTy) =>
    { type := .DEAD, locationNum := callIdx + 2 + i,
      code := Code.dead (Expr.symbol s!"__CPROVER__start::{argName}" argTy),
      sourceLoc := {function := "", line := 0, file := "", workingDir := ""}}
  {
    instructions := (#[
    -- CALL __CPROVER_initialize()
    { type := .FUNCTION_CALL, locationNum := locationNum + 1,
      code := { id := .function .functionCall, operands := [
        { id := .nullary .nil, type := Ty.Empty },
        { id := .nullary (.symbol "__CPROVER_initialize"), type := { id := .primitive .empty } },
        { id := .nullary (.symbol "arguments"), type := Ty.Empty }
      ]},
      sourceLoc := {function := "__CPROVER_initialize", line := 24, file := "<built-in-additions>", workingDir := ""}}
  ] ++ argInstructions.toArray ++ #[
    -- CALL return' := funcName(args...)
    { type := .FUNCTION_CALL, locationNum := callIdx,
      code := { id := .function .functionCall, operands := [
        { id := .nullary .nil, type := Ty.Empty },
        { id := .nullary (.symbol funcName), type := { id := .primitive .empty } },
        { id := .nullary (.symbol "arguments"), type := Ty.Empty }
      ]},
      sourceLoc := {function := funcName, line := 5, file := s!"{funcName}.c", workingDir := ""}},
    -- OUTPUT address_of("return'")
    { type := .OTHER, locationNum := callIdx + 1,
      sourceLoc := {function := funcName, line := 5, file := s!"{funcName}.c", workingDir := ""}}
  ] ++ deadInstructions.toArray ++ #[
    -- END_FUNCTION
    { type := .END_FUNCTION, locationNum := callIdx + 2 + args.length,
      sourceLoc := {function := "", line := 0, file := "", workingDir := ""}}
  ]) }


-- #eval genCProverStart "simpleAdd" [("simpleAdd::x", Ty.SignedBV 32), ("simpleAdd::y", Ty.SignedBV 32)] 8

-------------------------------------------------------------------------------

/-
int simpleAdd(int x, int y) {
  __CPROVER_assume(x > 0 && x < 0x0F000000);
  __CPROVER_assume(y > 0 && y < 0x0F000000);
  int z = x + y;
  return z;
}

-- GOTO Program before instrumentation
-- goto-cc simpleAdd.c -o simpleAdd.gb
-- # Textual representation of GOTO instructions.
-- cbmc simpleAdd.gb --function simpleAdd --show-goto-functions
-- # JSON representation of GOTO instructions.
-- cbmc simpleAdd.gb --function simpleAdd --show-goto-functions --json-ui > simpleAdd.goto.json


simpleAdd /* simpleAdd */
        // 0 file simpleAdd.c line 6 function simpleAdd
        ASSUME simpleAdd::x > 0 ∧ simpleAdd::x < 251658240
        // 1 file simpleAdd.c line 7 function simpleAdd
        ASSUME simpleAdd::y > 0 ∧ simpleAdd::y < 251658240
        // 2 file simpleAdd.c line 8 function simpleAdd
        DECL simpleAdd::1::z : signedbv[32]
        // 3 file simpleAdd.c line 8 function simpleAdd
        ASSERT ¬(overflow-+(simpleAdd::x, simpleAdd::y)) // arithmetic overflow on signed + in x + y
        // 4 file simpleAdd.c line 8 function simpleAdd
        ASSIGN simpleAdd::1::z := simpleAdd::x + simpleAdd::y
        // 5 file simpleAdd.c line 9 function simpleAdd
        SET RETURN VALUE simpleAdd::1::z
        // 6 file simpleAdd.c line 9 function simpleAdd
        DEAD simpleAdd::1::z
        // 7 file simpleAdd.c line 10 function simpleAdd
        END_FUNCTION
-/

/--
Hand-encoding of GOTO instructions to test the CBMC GOTO-JSON interface.
-/
private def simpleAddProgram : Program := {
  instructions := #[
    -- ASSUME simpleAdd::x > 0 ∧ simpleAdd::x < 251658240
    { type := .ASSUME, locationNum := 0,
      guard := Expr.and [(Expr.gt (Expr.symbol "simpleAdd::x" (Ty.SignedBV 32)) (Expr.constant "0" (Ty.SignedBV 32))),
                         (Expr.lt (Expr.symbol "simpleAdd::x" (Ty.SignedBV 32)) (Expr.constant "251658240" (Ty.SignedBV 32)))],
      sourceLoc := {function := "simpleAdd", line := 6, file := "simpleAdd.c", workingDir := ""}},

    -- ASSUME simpleAdd::y > 0 ∧ simpleAdd::y < 251658240
    { type := .ASSUME, locationNum := 1,
      guard := Expr.and [(Expr.gt (Expr.symbol "simpleAdd::y" (Ty.SignedBV 32)) (Expr.constant "0" (Ty.SignedBV 32))),
                         (Expr.lt (Expr.symbol "simpleAdd::y" (Ty.SignedBV 32)) (Expr.constant "251658240" (Ty.SignedBV 32)))],
      sourceLoc := {function := "simpleAdd", line := 7, file := "simpleAdd.c", workingDir := ""}},

    -- DECL simpleAdd::1::z : signedbv[32]
    { type := .DECL, locationNum := 2,
      code := Code.decl (Expr.symbol "simpleAdd::1::z" (Ty.SignedBV 32)),
      sourceLoc := {function := "simpleAdd", line := 8, file := "simpleAdd.c", workingDir := ""}},

    -- ASSERT ¬(overflow-+(simpleAdd::x, simpleAdd::y))
    { type := .ASSERT, locationNum := 3,
      guard := Expr.not (Expr.plus_overflow (Expr.symbol "simpleAdd::x" (Ty.SignedBV 32)) (Expr.symbol "simpleAdd::y" (Ty.SignedBV 32))),
      sourceLoc := {function := "simpleAdd", line := 8, file := "simpleAdd.c", workingDir := ""}},

    -- ASSIGN simpleAdd::1::z := simpleAdd::x + simpleAdd::y
    { type := .ASSIGN, locationNum := 4,
      code := Code.assign (Expr.symbol "simpleAdd::1::z" (Ty.SignedBV 32))
                          (Expr.add [Expr.symbol "simpleAdd::x" (Ty.SignedBV 32), Expr.symbol "simpleAdd::y" (Ty.SignedBV 32)]),
      sourceLoc := {function := "simpleAdd", line := 8, file := "simpleAdd.c", workingDir := ""}},

    -- SET RETURN VALUE simpleAdd::1::z
    { type := .SET_RETURN_VALUE, locationNum := 5,
      code := Code.set_return_value (Expr.symbol "simpleAdd::1::z" (Ty.SignedBV 32)),
      sourceLoc := {function := "simpleAdd", line := 9, file := "simpleAdd.c", workingDir := ""} },

    -- DEAD simpleAdd::1::z
    { type := .DEAD, locationNum := 6,
      code := Code.dead (Expr.symbol "simpleAdd::1::z" (Ty.SignedBV 32)),
      sourceLoc := {function := "simpleAdd", line := 9, file := "simpleAdd.c", workingDir := ""} },

    -- END_FUNCTION
    { type := .END_FUNCTION, locationNum := 7,
      sourceLoc := {function := "simpleAdd", line := 10, file := "simpleAdd.c", workingDir := ""}}
  ]
}

-- #eval programToJson "__CPROVER_initialize" (defaultCProverInitialize 21)

-- #eval programToJson "simpleAdd" simpleAddProgram

-- #eval programToJson "__CPROVER__start" (genCProverStart "simpleAdd" [("simpleAdd::x", Ty.SignedBV 32), ("simpleAdd::y", Ty.SignedBV 32)] 8)

-- #eval writeProgramsToFile "StrataTest/Backends/CBMC/simple.strata_goto.json"
--         [("__CPROVER__start", (genCProverStart "simpleAdd" [("simpleAdd::x", Ty.SignedBV 32), ("simpleAdd:y", Ty.SignedBV 32)]) 8),
--          ("simpleAdd", simpleAddProgram)]


-------------------------------------------------------------------------------

private def simpleAddUnsignedProgram : Program := {
  instructions := #[
    -- simpleAddUnsigned::x < 4294901760
    { type := .ASSUME, locationNum := 0,
      guard := Expr.lt (Expr.symbol "simpleAddUnsigned::x" (Ty.UnsignedBV 32)) (Expr.constant "4294901760" (Ty.UnsignedBV 32)),
      sourceLoc := {function := "simpleAddUnsigned", line := 6, file := "simpleAddUnsigned.c", workingDir := ""}},

    -- ASSUME simpleAddUnsigned::y < 4369
    { type := .ASSUME, locationNum := 1,
      guard := (Expr.lt (Expr.symbol "simpleAddUnsigned::y" (Ty.UnsignedBV 32)) (Expr.constant "4369" (Ty.UnsignedBV 32))),
      sourceLoc := {function := "simpleAddUnsigned", line := 7, file := "simpleAddUnsigned.c", workingDir := ""}},

    -- DECL simpleAddUnsigned::1::z : signedbv[32]
    { type := .DECL, locationNum := 2,
      code := Code.decl (Expr.symbol "simpleAddUnsigned::1::z" (Ty.UnsignedBV 32)),
      sourceLoc := {function := "simpleAddUnsigned", line := 8, file := "simpleAddUnsigned.c", workingDir := ""}},

    -- ASSIGN simpleAddUnsigned::1::z := simpleAddUnsigned::x + simpleAddUnsigned::y
    { type := .ASSIGN, locationNum := 4,
      code := Code.assign (Expr.symbol "simpleAddUnsigned::1::z" (Ty.UnsignedBV 32))
                          (Expr.add [Expr.symbol "simpleAddUnsigned::x" (Ty.UnsignedBV 32), Expr.symbol "simpleAddUnsigned::y" (Ty.UnsignedBV 32)]),
      sourceLoc := {function := "simpleAddUnsigned", line := 8, file := "simpleAddUnsigned.c", workingDir := ""}},

    -- ASSERT simpleAddUnsignedUnsigned::1::z < 4294906128
    { type := .ASSERT, locationNum := 3,
      guard := (Expr.lt (Expr.symbol "simpleAddUnsigned::1::z" (Ty.UnsignedBV 32)) (Expr.constant "4294906128" (Ty.UnsignedBV 32))),
      sourceLoc := {function := "simpleAddUnsigned", line := 8, file := "simpleAddUnsigned.c", workingDir := ""}},

    -- SET RETURN VALUE simpleAddUnsigned::1::z
    { type := .SET_RETURN_VALUE, locationNum := 5,
      code := Code.set_return_value (Expr.symbol "simpleAddUnsigned::1::z" (Ty.UnsignedBV 32)),
      sourceLoc := {function := "simpleAddUnsigned", line := 9, file := "simpleAddUnsigned.c", workingDir := ""} },

    -- DEAD simpleAddUnsigned::1::z
    { type := .DEAD, locationNum := 6,
      code := Code.dead (Expr.symbol "simpleAddUnsigned::1::z" (Ty.UnsignedBV 32)),
      sourceLoc := {function := "simpleAddUnsigned", line := 9, file := "simpleAddUnsigned.c", workingDir := ""} },

    -- END_FUNCTION
    { type := .END_FUNCTION, locationNum := 7,
      sourceLoc := {function := "simpleAddUnsigned", line := 10, file := "simpleAddUnsigned.c", workingDir := ""}}
  ]
}

-- #eval programToJson "simpleAddUnsigned" simpleAddUnsignedProgram
