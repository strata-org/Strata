/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boole.DDMTransform.Parse
import Strata.Languages.Core.Verifier
import Strata.DL.Imperative.Stmt

namespace BooleDDM

-- set_option trace.Strata.generator true in
#strata_gen Boole

end BooleDDM

namespace Strata.Boole

abbrev _root_.Strata.Boole.Type := BooleDDM.BooleType SourceRange
abbrev Expr := BooleDDM.Expr SourceRange
abbrev Program := BooleDDM.Program SourceRange

structure State where
  fvCtx : GlobalContext

abbrev TranslateM := StateT State (Except DiagnosticModel)

def getBVarName (m : SourceRange) (i : Nat) : TranslateM String := sorry

def getFVarName (m : SourceRange) (i : Nat) : TranslateM String := do
  match (← get).fvCtx.nameOf? i with
  | none => throw (.withRange ⟨⟨""⟩, m⟩ f!"Unknown free variable with index {i}")
  | some n => return n

def toCoreMonoType (t : Boole.Type) : TranslateM Lambda.LMonoTy := do
  match t with
  | .bvar m n => return .ftvar (← getBVarName m n)
  | .tvar _ n => return .ftvar n
  | .fvar m ft ats => return .tcons (← getFVarName m ft) (← ats.mapM toCoreMonoType).toList
  | .arrow _ α β => return .arrow (← toCoreMonoType α) (← toCoreMonoType β)
  | .bool _ => return .bool
  | .Map _ dom range => return .tcons "Map" [← toCoreMonoType dom, ← toCoreMonoType range]
  | _ => panic! "unsupported type: {t}"

def toCoreType (t : Boole.Type) : TranslateM Core.Expression.Ty :=
  return .forAll [] (← toCoreMonoType t)

def toCoreExpr (e : Boole.Expr) : TranslateM Core.Expression.Expr := do
  match e with
  | .fvar m n => return .fvar () (← getFVarName m n) .none
  | .bvar _ n => return .bvar () n
  | .app _ f a  => return .app () (← toCoreExpr f) (← toCoreExpr a)
  | _ => panic! "unsupported expression: {e}"

def toCoreProgram (program : Boole.Program) : Core.Program :=
  sorry

open Lean.Parser in
def getProgram (p : Strata.Program)
  : Except DiagnosticModel Boole.Program := do
  match BooleDDM.Program.ofAst p.commands[0]! with
  | .ok p    => return p
  | .error e => throw (.fromMessage e)

def typeCheck (p : Strata.Program) (options : Options := Options.default) :
  Except DiagnosticModel Core.Program := do
  match Boole.getProgram p with
  | .ok p => Core.typeCheck options (toCoreProgram p)
  | .error e => panic! s!"DDM Transform Error: {e}"

open Lean.Parser in
def verify
    (smtsolver : String) (env : Strata.Program)
    (ictx : InputContext := Inhabited.default)
    (proceduresToVerify : Option (List String) := none)
    (options : Options := Options.default)
    (tempDir : Option String := .none)
    : IO Core.VCResults := do
  match Boole.getProgram env with
  | .error e => panic! s!"DDM Transform Error: {e}"
  | .ok p =>
    let runner tempDir :=
      EIO.toIO (fun dm => IO.Error.userError (toString (dm.format (some ictx.fileMap))))
        (Core.verify smtsolver (toCoreProgram p) tempDir proceduresToVerify options)
    match tempDir with
    | .none =>
      IO.FS.withTempDir runner
    | .some p =>
      IO.FS.createDirAll ⟨p⟩
      runner ⟨p⟩

end Strata.Boole
