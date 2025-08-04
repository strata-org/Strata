/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.DL.Imperative.Arith
import StrataTest.DL.Imperative.DDMDefinition

namespace ArithPrograms
open Std (ToFormat Format format)

/-!

## Translation of Concrete Syntax into Abstract Syntax

`ArithPrograms`' Concrete Syntax is defined in the file `DDMDefinition.lean` and
Abstract Syntax is in the file `ArithExpr.lean`.
-/

---------------------------------------------------------------------

structure TransState where
  errors : Array Format

def TransM := StateM TransState
  deriving Monad

def TransM.run (m : TransM α) : (α × Array Format) :=
  let (v, s) := StateT.run m { errors := #[] }
  (v, s.errors)

def TransM.error [Inhabited α] (msg : Format) : TransM α := do
  fun s => ((), { errors := s.errors.push msg })
  return panic (toString msg)

structure TransBindings where
  freeVars : Array String := #[]
  varGen : Nat := 0

def incrGen (bindings : TransBindings) : TransBindings :=
  { bindings with varGen := bindings.varGen + 1 }

def genInitVar (bindings : TransBindings) (name : String) : String × TransBindings :=
  let name := ("init_" ++ name ++ "_" ++ (toString bindings.varGen))
  (name, incrGen bindings)

instance : ToFormat TransBindings where
  format b := f!"freeVars: {b.freeVars}\n\
                 varGen: {b.varGen}"

instance : Inhabited (TransBindings × Arith.Command) where
  default := ({}, .havoc "default_var")

/--
info: inductive ArithPrograms.ArithProgramsType : Type
number of parameters: 0
constructors:
ArithPrograms.ArithProgramsType.bool : ArithProgramsType
ArithPrograms.ArithProgramsType.num : ArithProgramsType
-/
#guard_msgs in
#print ArithProgramsType

def translateType (tp : ArithProgramsType) : Arith.Ty :=
  match tp with
  | .num => .Num
  | .bool => .Bool

/--
info: inductive ArithPrograms.Expr : Type
number of parameters: 0
constructors:
ArithPrograms.Expr.fvar : Nat → Expr
ArithPrograms.Expr.numLit : Nat → Expr
ArithPrograms.Expr.btrue : Expr
ArithPrograms.Expr.bfalse : Expr
ArithPrograms.Expr.add_expr : Expr → Expr → Expr
ArithPrograms.Expr.mul_expr : Expr → Expr → Expr
ArithPrograms.Expr.eq_expr : ArithProgramsType → Expr → Expr → Expr
-/
#guard_msgs in
#print Expr

def translateExpr (bindings : TransBindings) (e : ArithPrograms.Expr) : TransM Arith.Expr := do
  match e with
  | .fvar i =>
    assert! i < bindings.freeVars.size
    let id := bindings.freeVars[i]!
    return (.Var id .none)
  | .numLit n => return (.Num n)
  | .btrue => return (.Bool true)
  | .bfalse => return (.Bool false)
  | .add_expr e1 e2 =>
    let e1 ← translateExpr bindings e1
    let e2 ← translateExpr bindings e2
    return (.Plus e1 e2)
  | .mul_expr e1 e2 =>
    let e1 ← translateExpr bindings e1
    let e2 ← translateExpr bindings e2
    return (.Mul e1 e2)
  | .eq_expr _ e1 e2 =>
    let e1 ← translateExpr bindings e1
    let e2 ← translateExpr bindings e2
    return (.Eq e1 e2)

/--
info: inductive ArithPrograms.Label : Type
number of parameters: 0
constructors:
ArithPrograms.Label.label : String → Label
-/
#guard_msgs in
#print Label

def translateLabel (_bindings : TransBindings) (e : ArithPrograms.Label) : TransM String := do
  match e with | .label s => return s

/--
info: inductive ArithPrograms.Command : Type
number of parameters: 0
constructors:
ArithPrograms.Command.init : String → ArithProgramsType → Expr → Command
ArithPrograms.Command.var : String → ArithProgramsType → Command
ArithPrograms.Command.assign : String → Expr → Command
ArithPrograms.Command.assume : Label → Expr → Command
ArithPrograms.Command.assert : Label → Expr → Command
ArithPrograms.Command.havoc : String → Command
-/
#guard_msgs in
#print Command

instance : Inhabited (Arith.Command × TransBindings) where
  default := (.havoc "default", {})

instance : Inhabited (Arith.Commands × TransBindings) where
  default := ([], {})

def translateCommand (bindings : TransBindings) (c : ArithPrograms.Command) :
  TransM (Arith.Command × TransBindings) := do
  match c with
  | .var name tp =>
    let bindings := { bindings with freeVars := bindings.freeVars ++ [name] }
    let tp := translateType tp
    let (init_var_name, bindings) := genInitVar bindings name
    return ((.init name tp (.Var init_var_name tp)), bindings)
  | .init name tp expr =>
    let tp := translateType tp
    let expr ← translateExpr bindings expr
    let bindings := { bindings with freeVars := bindings.freeVars ++ [name] }
    return ((.init name tp expr), bindings)
  | .assign label expr =>
    let expr ← translateExpr bindings expr
    return ((.set label expr), bindings)
  | .assume label expr =>
    let label ← translateLabel bindings label
    let expr ← translateExpr bindings expr
    return ((.assume label expr), bindings)
  | .assert label expr =>
    let label ← translateLabel bindings label
    let expr ← translateExpr bindings expr
    return ((.assert label expr), bindings)
  | .havoc name =>
    return ((.havoc name), bindings)

partial def translateProgram (ops : Array Strata.Operation) : TransM Arith.Commands := do
  let (cmds, _) ← go 0 ops.size {} ops
  return cmds
  where go (count max : Nat) (bindings : TransBindings) (ops : Array Strata.Operation)
      : TransM (Arith.Commands × TransBindings) := do
  match (max - count) with
  | 0 => return ([], bindings)
  | _ + 1 =>
    let op := ops[count]!
    match Command.ofAst op with
    | .error e => TransM.error f!"{e}"
    | .ok cmd =>
      let (cmd, bindings) ← translateCommand bindings cmd
      let (cmds, bindings) ← go (count + 1) max bindings ops
      return ((cmd :: cmds), bindings)

end ArithPrograms
---------------------------------------------------------------------

section
open ArithPrograms

private def testEnv :=
#strata
program ArithPrograms;
var x : num;
assert [test]: (1 == 2);
var y : num;
#end

/-- info: (translateProgram testEnv.commands).run : Arith.Commands × Array Std.Format -/
#guard_msgs in
#check TransM.run (translateProgram (testEnv.commands))

/--
info: init (x : Num) := (init_x_0 : Num)
assert [test] 1 = 2
init (y : Num) := (init_y_1 : Num)
-/
#guard_msgs in
#eval let (cmds, errors) := TransM.run (translateProgram (testEnv.commands))
      if errors.isEmpty then
        Std.format cmds
      else
        Std.Format.joinSep errors.toList "{Format.line}"

end section

---------------------------------------------------------------------
