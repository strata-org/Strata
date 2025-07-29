/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.DDMTransform.Translate
import Strata.Languages.Boogie.Verifier
import Strata.DL.Imperative.Stmt

namespace Strata

-- Verification is done by:
-- 1. Translating to loop-free program
-- 2. Running SymExec of Lambda and Imp


def translate_expr (e : Loopy.DefaultPureExpr.Expr) : Lambda.LExpr Boogie.BoogieIdent :=
  match e with
  | .const c ty => .const c ty
  | .op o ty => .op (.unres, o) ty
  | .bvar n => .bvar n
  | .fvar n ty => .fvar (.unres, n) ty
  | .mdata i e => .mdata i (translate_expr e)
  | .abs ty e => .abs ty (translate_expr e)
  | .quant k ty e => .quant k ty (translate_expr e)
  | .app fn e => .app (translate_expr fn) (translate_expr e)
  | .ite c t e => .ite (translate_expr c) (translate_expr t) (translate_expr e)
  | .eq e1 e2 => .eq (translate_expr e1) (translate_expr e2)

def translate_cmd (c: Loopy.Command) : Boogie.Command :=
  match c with
  | .init name ty e _md => .cmd (.init (.unres, name) ty (translate_expr e) {})
  | .set name e _md => .cmd (.set (.unres, name) (translate_expr e) {})
  | .havoc name _md => .cmd (.havoc (.unres, name) {})
  | .assert label b _md => .cmd (.assert label (translate_expr b) {})
  | .assume label b _md =>  .cmd (.assume label (translate_expr b) {})

partial def translate_stmt (s: Imperative.Stmt Loopy.DefaultPureExpr Loopy.Command) : Boogie.Statement :=
  match s with
  | .cmd c => .cmd (translate_cmd c)
  | .block l b _md => .block l {ss := b.ss.map translate_stmt} {}
  | .ite cond thenb elseb _md => .ite (translate_expr cond) {ss := thenb.ss.map translate_stmt} {ss := elseb.ss.map translate_stmt} {}
  | .goto label _md => .goto label {}

def loop_elimination_statement(s : Loopy.LoopOrStmt) : Boogie.Statement :=
  match s with
  | .loop guard body measure invariant =>
    match measure, invariant with
    | .some measure, some invariant =>
      -- let bodyss : := body.ss
      let assigned_vars := (Imperative.Stmts.modifiedVars body.ss).map (λ s => (.unres, s))
      let havocd : Boogie.Statement := .block "loop havoc" {ss:= assigned_vars.map (λ n => Boogie.Statement.havoc n {})} {}

      let measure_pos := (.app (.app (.op "Int.Ge" none) (translate_expr measure)) (.const "0" none))

      let entry_invariant : Boogie.Statement := .assert "entry_invariant" (translate_expr invariant) {}
      let assert_measure_positive : Boogie.Statement := .assert "assert measure_pos" measure_pos {}
      let first_iter_facts : Boogie.Statement := .ite (translate_expr guard) {ss := [entry_invariant, assert_measure_positive]} {ss := []} {}

      let arbitrary_iter_assumes := .block "arbitrary_iter_assumes" {ss := [(Boogie.Statement.assume "assume_guard" (translate_expr guard) {}), (Boogie.Statement.assume "assume_invariant" (translate_expr invariant) {}), (Boogie.Statement.assume "assume_measure_pos" measure_pos {})]} {}
      let measure_old_value_assign : Boogie.Statement := .init "special-name-for-old-measure-value" (.forAll [] (.tcons "int" [])) (translate_expr measure) {}
      let measure_decreases : Boogie.Statement := .assert "measure_decreases" (.app (.app (.op "Int.Lt" none) (translate_expr measure)) (.fvar "special-name-for-old-measure-value" none)) {}
      let measure_imp_not_guard : Boogie.Statement := .assert "measure_imp_not_guard" (.ite (.app (.app (.op "Int.Le" none) (translate_expr measure)) (.const "0" none)) (.app (.op "Bool.Not" none) (translate_expr guard)) (.const "true" none)) {}
      let maintain_invariant : Boogie.Statement := .assert "arbitrary_iter_maintain_invariant" (translate_expr invariant) {}
      let body_statements : List Boogie.Statement := body.ss.map translate_stmt
      let arbitrary_iter_facts : Boogie.Statement := .block "arbitrary iter facts" {ss := [havocd, arbitrary_iter_assumes, measure_old_value_assign] ++ body_statements ++ [measure_decreases, measure_imp_not_guard, maintain_invariant]} {}

      let not_guard : Boogie.Statement := .assume "not_guard" (.app (.op "Bool.Not" none) (translate_expr guard)) {}
      let invariant : Boogie.Statement := .assume "invariant" (translate_expr invariant) {}

      .block "transformed loop block" {ss := [first_iter_facts, arbitrary_iter_facts, havocd, not_guard, invariant]} {}
    | _, _ => panic! "Loop elimination require measure and invariant"
  | .stmt s => translate_stmt s

-- C_Simp functions are Boogie procedures
def loop_elimination_function(f : C_Simp.Function) : Boogie.Procedure :=
  let boogie_preconditions := [("pre", {expr := translate_expr f.pre})]
  let boogie_postconditions := [("post", {expr := translate_expr f.post})]
  {header := {name := f.name, typeArgs := [],
              inputs := f.inputs.map (λ p => (p.fst, p.snd)),
              outputs := [("return", f.ret_ty)]},
              spec := {modifies := [],
                       preconditions := boogie_preconditions,
                       postconditions := boogie_postconditions},
                       body := f.body.map loop_elimination_statement}


def loop_elimination(program : C_Simp.Program) : Boogie.Program :=
  {decls := program.funcs.map (λ f => .proc (loop_elimination_function f) {})}

-- Do loop elimination
def to_boogie(program : C_Simp.Program) : Boogie.Program :=
  loop_elimination program

-- def C_Simp.verify (program : C_Simp.Program) :
--   IO Boogie.VCResults := do
--   EIO.toIO (fun f => IO.Error.userError (toString f)) (Boogie.verify "cvc5" (to_boogie program) false)

def C_Simp.get_program (env: Environment) : C_Simp.Program :=
  (Strata.C_Simp.TransM.run (Strata.C_Simp.translateProgram (env.commands))).fst

def C_Simp.verify (smtsolver : String) (env : Environment) (options : Options := Options.default):
  IO Boogie.VCResults := do
  let program := C_Simp.get_program env
  EIO.toIO (fun f => IO.Error.userError (toString f))
    (Boogie.verify smtsolver (to_boogie program) options)

end Strata
