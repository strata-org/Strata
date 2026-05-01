/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.C_Simp.C_Simp
public import Strata.Languages.C_Simp.DDMTransform.Translate
public import Strata.Languages.Core.Options
public import Strata.Languages.Core.Verifier
import Lean.Parser.Types
import Strata.Languages.Core.CoreOp
import Strata.DL.Imperative.Stmt

public section

open Core

namespace Strata

-- Verification is done by:
-- 1. Translating to loop-free program
-- 2. Running SymExec of Lambda and Imp


-- nosourcerange-file: C_Simp expressions carry Unit metadata, so no source range is available
/-- Translate a C_Simp expression to a Core expression.
    C_Simp expressions carry `Unit` metadata, so no source range is available. -/
def translate_expr (e : C_Simp.Expression.Expr) : Lambda.LExpr Core.CoreLParams.mono :=
  match e with
  | .const _ c => .const ExprSourceLoc.none c
  | .op _ o ty => .op ExprSourceLoc.none ⟨o.name, ()⟩ ty
  | .bvar _ n => .bvar ExprSourceLoc.none n
  | .fvar _ n ty => .fvar ExprSourceLoc.none ⟨n.name, ()⟩ ty
  | .abs _ name ty e => .abs ExprSourceLoc.none name ty (translate_expr e)
  | .quant _ k name ty tr e => .quant ExprSourceLoc.none k name ty (translate_expr tr) (translate_expr e)
  | .app _ fn e => .app ExprSourceLoc.none (translate_expr fn) (translate_expr e)
  | .ite _ c t e => .ite ExprSourceLoc.none (translate_expr c) (translate_expr t) (translate_expr e)
  | .eq _ e1 e2 => .eq ExprSourceLoc.none (translate_expr e1) (translate_expr e2)

def translate_opt_expr (e : Option C_Simp.Expression.Expr) : Option (Lambda.LExpr Core.CoreLParams.mono) :=
  match e with
  | some e => translate_expr e
  | none => none

def translate_cmd (c: C_Simp.Command) : Core.Command :=
  match c with
  | .init name ty e _md =>
    let e' := e.map translate_expr
    .cmd (.init ⟨name.name, ()⟩ ty e' {})
  | .set name e _md =>
    let e' := e.map translate_expr
    .cmd (.set ⟨name.name, ()⟩ e' {})
  | .assert label b _md => .cmd (.assert label (translate_expr b) {})
  | .assume label b _md =>  .cmd (.assume label (translate_expr b) {})
  | .cover label b _md =>  .cmd (.cover label (translate_expr b) {})

def translate_stmt (s: Imperative.Stmt C_Simp.Expression C_Simp.Command) : Core.Statement :=
  match s with
  | .cmd c => .cmd (translate_cmd c)
  | .block l b _md => .block l (b.map translate_stmt) {}
  | .ite cond thenb elseb _md =>
    .ite (cond.map translate_expr) (thenb.map translate_stmt) (elseb.map translate_stmt) {}
  | .loop guard measure invariant body _md =>
    .loop (guard.map translate_expr) (translate_opt_expr measure)
      (invariant.map (fun (l, e) => (l, translate_expr e))) (body.map translate_stmt) {}
  | .funcDecl _ _ => panic! "C_Simp does not support function declarations"
  | .typeDecl _ _ => panic! "C_Simp does not support type declarations"
  | .exit label _md => .exit label {}


/--
Eliminates loops and replaces them with the following:

```
Proof obligation that invariant holds on entry
Proof obligation that invariant holds after arbitrary iteration
  (assuming invariant and guard held at start)

Proof obligation that measure is positive on entry
Proof obligation that measure <= 0 implies guard is false
Proof obligation that measure decreases on arbitrary iteration

Assumption that guard is false on exit
Assumption that invariant holds on exit
```

This is suitable for Symbolic Execution, but may not be suitable for
other analyses.

Synthesized expressions (measure checks, guard negations) use `ExprSourceLoc.none`
because they have no corresponding source location.
-/
def loop_elimination_statement(s : C_Simp.Statement) : Core.Statement :=
  match s with
  | .loop guard measure invList body _ =>
    match guard, measure, invList with
    | .det guard_expr, .some measure, _ =>
      let assigned_vars := (Imperative.Block.modifiedVars body).map (λ s => ⟨s.name, ()⟩)
      let havocd : Core.Statement := .block "loop havoc" (assigned_vars.map (λ n => Core.Statement.havoc n {})) {}

      let measure_pos := (.app ExprSourceLoc.none (.app ExprSourceLoc.none (coreOpExpr (.numeric ⟨.int, .Ge⟩)) (translate_expr measure)) (.intConst ExprSourceLoc.none 0))

      let entry_invariants : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assert s!"entry_invariant_{i}" (translate_expr inv) {}
      let assert_measure_positive : Core.Statement := .assert "assert_measure_pos" measure_pos {}
      let first_iter_facts : Core.Statement := .block "first_iter_asserts" (entry_invariants ++ [assert_measure_positive]) {}

      let inv_assumes : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        Core.Statement.assume s!"assume_invariant_{i}" (translate_expr inv) {}
      let arbitrary_iter_assumes := .block "arbitrary_iter_assumes"
        ([Core.Statement.assume "assume_guard" (translate_expr guard_expr) {}] ++ inv_assumes ++
         [Core.Statement.assume "assume_measure_pos" measure_pos {}]) {}
      let measure_old_value_assign : Core.Statement := .init "special-name-for-old-measure-value" (.forAll [] (.tcons "int" [])) (.det (translate_expr measure)) {}
      let measure_decreases : Core.Statement := .assert "measure_decreases" (.app ExprSourceLoc.none (.app ExprSourceLoc.none (coreOpExpr (.numeric ⟨.int, .Lt⟩)) (translate_expr measure)) (.fvar ExprSourceLoc.none "special-name-for-old-measure-value" none)) {}
      let measure_imp_not_guard : Core.Statement := .assert "measure_imp_not_guard" (.ite ExprSourceLoc.none (.app ExprSourceLoc.none (.app ExprSourceLoc.none (coreOpExpr (.numeric ⟨.int, .Le⟩)) (translate_expr measure)) (.intConst ExprSourceLoc.none 0)) (.app ExprSourceLoc.none (coreOpExpr (.bool .Not)) (translate_expr guard_expr)) Core.true) {}
      let maintain_invariants : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assert s!"arbitrary_iter_maintain_invariant_{i}" (translate_expr inv) {}
      let body_statements : List Core.Statement := body.map translate_stmt
      let arbitrary_iter_facts : Core.Statement := .block "arbitrary iter facts"
        ([havocd, arbitrary_iter_assumes, measure_old_value_assign] ++ body_statements ++
         [measure_decreases, measure_imp_not_guard] ++ maintain_invariants) {}

      let not_guard : Core.Statement := .assume "not_guard" (.app ExprSourceLoc.none (coreOpExpr (.bool .Not)) (translate_expr guard_expr)) {}
      let invariant_assumes : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assume s!"invariant_{i}" (translate_expr inv) {}

      .ite (.det (translate_expr guard_expr)) ([first_iter_facts, arbitrary_iter_facts, havocd, not_guard] ++ invariant_assumes) [] {}
    | .det guard_expr, .none, _ =>
      let assigned_vars := (Imperative.Block.modifiedVars body).map (λ s => ⟨s.name, ()⟩)
      let havocd : Core.Statement := .block "loop havoc" (assigned_vars.map (λ n => Core.Statement.havoc n {})) {}
      let entry_invariants : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assert s!"entry_invariant_{i}" (translate_expr inv) {}
      let first_iter_facts : Core.Statement := .block "first_iter_asserts" entry_invariants {}
      let inv_assumes : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        Core.Statement.assume s!"assume_invariant_{i}" (translate_expr inv) {}
      let arbitrary_iter_assumes := .block "arbitrary_iter_assumes"
        ([Core.Statement.assume "assume_guard" (translate_expr guard_expr) {}] ++ inv_assumes) {}
      let maintain_invariants : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assert s!"arbitrary_iter_maintain_invariant_{i}" (translate_expr inv) {}
      let body_statements : List Core.Statement := body.map translate_stmt
      let arbitrary_iter_facts : Core.Statement := .block "arbitrary iter facts"
        ([havocd, arbitrary_iter_assumes] ++ body_statements ++ maintain_invariants) {}
      let not_guard : Core.Statement := .assume "not_guard" (.app ExprSourceLoc.none (coreOpExpr (.bool .Not)) (translate_expr guard_expr)) {}
      let invariant_assumes : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assume s!"invariant_{i}" (translate_expr inv) {}
      .ite (.det (translate_expr guard_expr)) ([first_iter_facts, arbitrary_iter_facts, havocd, not_guard] ++ invariant_assumes) [] {}
    | .nondet, _, _ =>
      let assigned_vars := (Imperative.Block.modifiedVars body).map (λ s => ⟨s.name, ()⟩)
      let havocd : Core.Statement := .block "loop havoc" (assigned_vars.map (λ n => Core.Statement.havoc n {})) {}
      let entry_invariants : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assert s!"entry_invariant_{i}" (translate_expr inv) {}
      let entry_invariant_assumes : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assume s!"assume_entry_invariant_{i}" (translate_expr inv) {}
      let first_iter_facts : Core.Statement := .block "first_iter_asserts" (entry_invariants ++ entry_invariant_assumes) {}
      let inv_assumes : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assume s!"assume_invariant_{i}" (translate_expr inv) {}
      let arbitrary_iter_assumes := .block "arbitrary_iter_assumes" inv_assumes {}
      let maintain_invariants : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assert s!"arbitrary_iter_maintain_invariant_{i}" (translate_expr inv) {}
      let body_statements : List Core.Statement := body.map translate_stmt
      let arbitrary_iter_facts : Core.Statement := .block "arbitrary iter facts"
        ([havocd, arbitrary_iter_assumes] ++ body_statements ++ maintain_invariants) {}
      let invariant_assumes : List Core.Statement := invList.mapIdx fun i (_, inv) =>
        .assume s!"invariant_{i}" (translate_expr inv) {}
      let exit_state_assumes := [havocd] ++ invariant_assumes
      let loop_passive := .ite .nondet (arbitrary_iter_facts :: exit_state_assumes) [] {}
      .block "loop" [first_iter_facts, loop_passive] {}
  | _ => translate_stmt s

-- C_Simp functions are Strata Core procedures
def loop_elimination_function(f : C_Simp.Function) : Core.Procedure :=
  let core_preconditions := [("pre", {expr := translate_expr f.pre, md := .empty })]
  let core_postconditions := [("post", {expr := translate_expr f.post, md := .empty })]
  {header := {name := f.name.name, typeArgs := [],
              inputs := f.inputs.map (λ p => (p.fst.name, p.snd)),
              outputs := [("return", f.ret_ty)]},
              spec := {preconditions := core_preconditions,
                       postconditions := core_postconditions},
                       body := f.body.map loop_elimination_statement}


def loop_elimination(program : C_Simp.Program) : Core.Program :=
  {decls := program.funcs.map (λ f => .proc (loop_elimination_function f) {})}

-- Do loop elimination
def to_core(program : C_Simp.Program) : Core.Program :=
  loop_elimination program

def C_Simp.get_program (p : Strata.Program) : C_Simp.Program :=
  (Strata.C_Simp.TransM.run Inhabited.default (Strata.C_Simp.translateProgram (p.commands))).fst

def C_Simp.typeCheck (p : Strata.Program) (options : VerifyOptions := .default):
  Except DiagnosticModel Core.Program := do
  let program := C_Simp.get_program p
  Core.typeCheck options (to_core program)

def C_Simp.verify (p : Strata.Program)
    (options : VerifyOptions := .default)
    (tempDir : Option String := .none):
  IO Core.VCResults := do
  let program := C_Simp.get_program p
  let runner tempDir := EIO.toIO (fun f => IO.Error.userError (toString f))
    (Core.verify (to_core program) tempDir .none options)
  match tempDir with
  | .none =>
    IO.FS.withTempDir runner
  | .some p =>
    IO.FS.createDirAll ⟨p⟩
    runner ⟨p⟩

end Strata
