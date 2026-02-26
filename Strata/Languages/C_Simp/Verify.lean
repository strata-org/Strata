/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.DDMTransform.Translate
import Strata.Languages.Core.Verifier
import Strata.DL.Imperative.Stmt

namespace Strata

-- Verification is done by:
-- 1. Translating to loop-free program
-- 2. Running SymExec of Lambda and Imp


/-- Convert C_Simp expression metadata (Unit) to Core expression metadata (SourceRange).
    C_Simp does not track source locations, so we use SourceRange.none. -/
private def csimpMetaToCore (_ : C_Simp.CSimpLParams.mono.base.Metadata) : Core.CoreLParams.mono.base.Metadata :=
  Strata.SourceRange.none

def translate_expr (e : C_Simp.Expression.Expr) : Lambda.LExpr Core.CoreLParams.mono :=
  match e with
  | .const m c => .const (csimpMetaToCore m) c
  | .op m o ty => .op (csimpMetaToCore m) ⟨o.name, .unres⟩ ty
  | .bvar m n => .bvar (csimpMetaToCore m) n
  | .fvar m n ty => .fvar (csimpMetaToCore m) ⟨n.name, .unres⟩ ty
  | .abs m ty e => .abs (csimpMetaToCore m) ty (translate_expr e)
  | .quant m k ty tr e => .quant (csimpMetaToCore m) k ty (translate_expr tr) (translate_expr e)
  | .app m fn e => .app (csimpMetaToCore m) (translate_expr fn) (translate_expr e)
  | .ite m c t e => .ite (csimpMetaToCore m) (translate_expr c) (translate_expr t) (translate_expr e)
  | .eq m e1 e2 => .eq (csimpMetaToCore m) (translate_expr e1) (translate_expr e2)

def translate_opt_expr (e : Option C_Simp.Expression.Expr) : Option (Lambda.LExpr Core.CoreLParams.mono) :=
  match e with
  | some e => translate_expr e
  | none => none

def translate_cmd (c: C_Simp.Command) : Core.Command :=
  match c with
  | .init name ty e _md => .cmd (.init ⟨name.name, .unres⟩ ty (translate_opt_expr e) {})
  | .set name e _md => .cmd (.set ⟨name.name, .unres⟩ (translate_expr e) {})
  | .havoc name _md => .cmd (.havoc ⟨name.name, .unres⟩ {})
  | .assert label b _md => .cmd (.assert label (translate_expr b) {})
  | .assume label b _md =>  .cmd (.assume label (translate_expr b) {})
  | .cover label b _md =>  .cmd (.cover label (translate_expr b) {})

def translate_stmt (s: Imperative.Stmt C_Simp.Expression C_Simp.Command) : Core.Statement :=
  match s with
  | .cmd c => .cmd (translate_cmd c)
  | .block l b _md => .block l (b.map translate_stmt) {}
  | .ite cond thenb elseb _md => .ite (translate_expr cond) (thenb.map translate_stmt) (elseb.map translate_stmt) {}
  | .loop guard measure invariant body _md => .loop (translate_expr guard) (translate_opt_expr measure) (invariant.map translate_expr) (body.map translate_stmt) {}
  | .funcDecl _ _ => panic! "C_Simp does not support function declarations"
  | .goto label _md => .goto label {}


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
-/
def loop_elimination_statement(s : C_Simp.Statement) : Core.Statement :=
  match s with
  | .loop guard measure invList body _ =>
    match measure, invList with
    | .some measure, _ =>
      -- let bodyss : := body.ss
      let assigned_vars := (Imperative.Block.modifiedVars body).map (λ s => ⟨s.name, .unres⟩)
      let havocd : Core.Statement := .block "loop havoc" (assigned_vars.map (λ n => Core.Statement.havoc n {})) {}

      -- Synthesized Core expressions have no C_Simp source location; SourceRange.none is used.
      let measure_pos := (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "Int.Ge" none) (translate_expr measure)) (.intConst Strata.SourceRange.none 0))

      let entry_invariants : List Core.Statement := invList.mapIdx fun i inv =>
        .assert s!"entry_invariant_{i}" (translate_expr inv) {}
      let assert_measure_positive : Core.Statement := .assert "assert_measure_pos" measure_pos {}
      let first_iter_facts : Core.Statement := .block "first_iter_asserts" (entry_invariants ++ [assert_measure_positive]) {}

      let inv_assumes : List Core.Statement := invList.mapIdx fun i inv =>
        Core.Statement.assume s!"assume_invariant_{i}" (translate_expr inv) {}
      let arbitrary_iter_assumes := .block "arbitrary_iter_assumes"
        ([Core.Statement.assume "assume_guard" (translate_expr guard) {}] ++ inv_assumes ++
         [Core.Statement.assume "assume_measure_pos" measure_pos {}]) {}
      let measure_old_value_assign : Core.Statement := .init "special-name-for-old-measure-value" (.forAll [] (.tcons "int" [])) (some (translate_expr measure)) {}
      let measure_decreases : Core.Statement := .assert "measure_decreases" (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "Int.Lt" none) (translate_expr measure)) (.fvar Strata.SourceRange.none "special-name-for-old-measure-value" none)) {}
      let measure_imp_not_guard : Core.Statement := .assert "measure_imp_not_guard" (.ite Strata.SourceRange.none (.app Strata.SourceRange.none (.app Strata.SourceRange.none (.op Strata.SourceRange.none "Int.Le" none) (translate_expr measure)) (.intConst Strata.SourceRange.none 0)) (.app Strata.SourceRange.none (.op Strata.SourceRange.none "Bool.Not" none) (translate_expr guard)) (.true Strata.SourceRange.none)) {}
      let maintain_invariants : List Core.Statement := invList.mapIdx fun i inv =>
        .assert s!"arbitrary_iter_maintain_invariant_{i}" (translate_expr inv) {}
      let body_statements : List Core.Statement := body.map translate_stmt
      let arbitrary_iter_facts : Core.Statement := .block "arbitrary iter facts"
        ([havocd, arbitrary_iter_assumes, measure_old_value_assign] ++ body_statements ++
         [measure_decreases, measure_imp_not_guard] ++ maintain_invariants) {}

      let not_guard : Core.Statement := .assume "not_guard" (.app Strata.SourceRange.none (.op Strata.SourceRange.none "Bool.Not" none) (translate_expr guard)) {}
      let invariant_assumes : List Core.Statement := invList.mapIdx fun i inv =>
        .assume s!"invariant_{i}" (translate_expr inv) {}

      .ite (translate_expr guard) ([first_iter_facts, arbitrary_iter_facts, havocd, not_guard] ++ invariant_assumes) [] {}
    | _, _ => panic! "Loop elimination require measure and invariant"
  | _ => translate_stmt s

-- C_Simp functions are Strata Core procedures
def loop_elimination_function(f : C_Simp.Function) : Core.Procedure :=
  let core_preconditions := [("pre", {expr := translate_expr f.pre, md := .empty })]
  let core_postconditions := [("post", {expr := translate_expr f.post, md := .empty })]
  {header := {name := f.name.name, typeArgs := [],
              inputs := f.inputs.map (λ p => (p.fst.name, p.snd)),
              outputs := [("return", f.ret_ty)]},
              spec := {modifies := [],
                       preconditions := core_preconditions,
                       postconditions := core_postconditions},
                       body := f.body.map loop_elimination_statement}


def loop_elimination(program : C_Simp.Program) : Core.Program :=
  {decls := program.funcs.map (λ f => .proc (loop_elimination_function f) {})}

-- Do loop elimination
def to_core(program : C_Simp.Program) : Core.Program :=
  loop_elimination program

def C_Simp.get_program (p : Strata.Program) : C_Simp.Program :=
  (Strata.C_Simp.TransM.run Inhabited.default (Strata.C_Simp.translateProgram (p.commands))).fst

def C_Simp.typeCheck (p : Strata.Program) (options : Options := Options.default):
  Except DiagnosticModel Core.Program := do
  let program := C_Simp.get_program p
  Core.typeCheck options (to_core program)

def C_Simp.verify (p : Strata.Program)
    (options : Options := Options.default)
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
