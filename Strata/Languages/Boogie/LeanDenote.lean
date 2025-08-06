/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

import Lean.Meta
import Lean.Elab.Command
import Strata.DL.Lambda.Reflect

namespace Strata
open Std (ToFormat Format format)
---------------------------------------------------------------------

open Boogie Lambda LTy.Syntax Imperative
open Lean Elab Tactic Expr Meta Command

syntax boolStx := &"true" <|> &"false"

syntax solverStx := atomic("(" &"solver" " := " (str) ")")
syntax verboseStx := atomic("(" &"verbose" " := " (boolStx) ")")
syntax checkOnlyStx := atomic("(" &"checkOnly" " := " (boolStx) ")")
syntax timeoutStx := atomic("(" &"timeout" " := " (num) ")")

syntax optionStx := solverStx <|> verboseStx <|> checkOnlyStx <|> timeoutStx

syntax (name := StrataBoogieVerify) "#verify"
          ws withoutPosition(ident)
          (ws withoutPosition(optionStx))*
          : command

def parseBoolStx : TSyntax ``boolStx → CommandElabM Bool
  | `(boolStx| true) => pure true
  | `(boolStx| false)  => pure false
  | _ => throwUnsupportedSyntax

def parseSolverStx : TSyntax ``solverStx → CommandElabM String
  | `(solverStx| (solver := $str)) => return str.getString
  | _ => throwUnsupportedSyntax

def parseVerboseStx : TSyntax ``verboseStx → CommandElabM Bool
  | `(verboseStx| (verbose := $ans)) => parseBoolStx ans
  | _ => throwUnsupportedSyntax

def parseCheckOnlyStx : TSyntax ``checkOnlyStx → CommandElabM Bool
  | `(checkOnlyStx| (checkOnly := $ans)) => parseBoolStx ans
  | _ => throwUnsupportedSyntax

def parseTimeOutStx : TSyntax ``timeoutStx → CommandElabM Nat
  | `(timeoutStx| (timeout := $ans)) => return ans.getNat
  | _ => throwUnsupportedSyntax

---------------------------------------------------------------------

private def mkImplication (assumptions : List Expression.Expr) (conclusion : Expression.Expr) :
    Expression.Expr :=
  match assumptions with
  | [] => conclusion
  | [a] =>
    LExpr.mkApp (.op "Bool.Implies" mty[bool → bool → bool]) [a, conclusion]
  | a :: arest =>
    let expr := mkImplication arest conclusion
    LExpr.mkApp (.op "Bool.Implies" mty[bool → bool → bool]) [a, expr]

def ProofObligation.toLExpr (ob : ProofObligation Expression) : Lambda.LExpr BoogieIdent :=
  let assumptions := ob.assumptions.flatten.map (fun (_, e) => e)
  mkImplication assumptions.reverse ob.obligation

instance : IdentifierString BoogieIdent where
  idToStr := fun (_, s) => s
  strToId := fun s => (.unres, s)

def VCResults.toExprs (vcs : VCResults) : MetaM (Array (String × Lean.Expr)) := do
  let mut res := #[]
  for vc in vcs do
    if vc.result != .unsat then
      let expr := ProofObligation.toLExpr vc.obligation
      let expr ← LExpr.toExpr expr
      res := res.push (vc.obligation.label, expr)
  return res

structure ThmsText where
  text : String
deriving TypeName

structure GenLeanVCThmsOutput where
  thms : String
  err : String
  warn : String
deriving TypeName

def VCResults.toTheoremsText (vcs : VCResults) : MetaM GenLeanVCThmsOutput := do
  let curr_ns ← getCurrNamespace
  let res ← VCResults.toExprs vcs
  let value ←  Lean.Meta.mkSorry (Lean.mkSort levelZero) false
  let mut thms := ""
  let mut err := ""
  let mut warn := ""
  for r in res do
    let name := Lean.Name.mkSimple r.fst
    let full_name := Lean.Name.append curr_ns name
    let type := r.snd
    let env ← getEnv
    match env.find? full_name with
    | some pre_exist_decl =>
      let msg := s!"Theorem {name} is already in the environment!\n"
      -- (FIXME): Why doesn't `Expr.equal` work here?
      -- if equal pre_exist_decl.type type then
      let type_str ← ppExpr type
      let pre_exist_type_str ← ppExpr pre_exist_decl.type
      if toString type_str == toString pre_exist_type_str then
        let has_sorry := pre_exist_decl.value!.hasSorry
        let msg := if has_sorry then
                    s!"\n" ++ msg ++ (s!"{bombEmoji} Note that theorem {name} was proved using `sorry`!\n")
                   else
                    s!"\n{checkEmoji} " ++ msg
        warn := warn ++ msg
      else
        let msg := s!"\n{crossEmoji} Theorem of name {name} is already \
                      in the environment, but its statement differs from \
                      the new conjecture! \n\
                      Existing theorem statement:\n\
                      {← ppExpr pre_exist_decl.type}\n\
                      New statement:\n\
                      {← ppExpr type}\n"
        err := err ++ msg
    | none =>
      let theoremText := s!"theorem {name} : {← ppExpr type} := {← ppExpr value}\n"
      thms := thms ++ theoremText
  return { thms := thms, err := err, warn := warn }

---------------------------------------------------------------------

unsafe def genVCTheoremsTextWithOptions (env : TSyntax `ident) (options : SMT.Options) :
    TermElabM GenLeanVCThmsOutput := do
  let envName := Lean.Name.append `Strata env.getId
  let some decl := (← getEnv).find? envName |
    throwError f!"Strata Environment {env} not found!"
  let (strata_env : Environment) ← evalExpr Environment (mkConst ``Environment) decl.value!
  let vc_results ← Strata.verify strata_env options
  logInfo f!"SMT Results:\n{vc_results}"
  let out ← VCResults.toTheoremsText vc_results
  return out

@[command_elab StrataBoogieVerify] unsafe def elabStrataBoogieVerify : CommandElab
  | `(command| #verify%$tk $env $opts*) => do
      let mut solverStr := SMT.Options.default.solver
      let mut verboseBool := SMT.Options.default.verbose
      let mut checkOnlyBool := SMT.Options.default.checkOnly
      let mut timeoutNat := SMT.Options.default.solverTimeout

      for opt in opts do
        match opt with
        | `(optionStx| $s:solverStx) => solverStr ← parseSolverStx s
        | `(optionStx| $v:verboseStx) => verboseBool ← parseVerboseStx v
        | `(optionStx| $c:checkOnlyStx) => checkOnlyBool ← parseCheckOnlyStx c
        | `(optionStx| $t:timeoutStx) => timeoutNat ← parseTimeOutStx t
        | _ => continue

      let options : SMT.Options := {
        solver := solverStr,
        verbose := verboseBool,
        checkOnly := checkOnlyBool,
        solverTimeout := timeoutNat
      }

      let out ← liftTermElabM (genVCTheoremsTextWithOptions env options)
      if not out.err.isEmpty then
        logErrorAt tk s!"{out.err}"
      if not out.warn.isEmpty then
        logInfoAt tk s!"{out.warn}"
      pushInfoLeaf (.ofCustomInfo { stx := ← getRef, value := Dynamic.mk (ThmsText.mk out.thms) })
  | _ => throwUnsupportedSyntax

mutual
partial def customNodeFromTree (t : InfoTree) : Option (Syntax × ThmsText) := do
  match t with
  | .node (.ofCustomInfo { stx, value }) _ =>
    let out := (← value.get? (ThmsText))
    return (stx, out)
    -- return (stx, (← value.get? (GenLeanVCThmsOutput)).res)
  | .node _ ts => customNodeFromTrees ts
  | .context _ t => customNodeFromTree t
  | _ => none

partial def customNodeFromTrees (ts : PersistentArray InfoTree) :
    Option (Syntax × ThmsText) := Id.run do
  let mut result := Option.none
  for t in ts do
    match customNodeFromTree t with
    | none => continue
    | some ans => result := ans; break
  return result
end

open Server CodeAction Elab Command RequestM in
@[command_code_action StrataBoogieVerify]
def strataBoogieVerifyAction : CommandCodeAction := fun _ _ _ node => do
  let .node _ ts := node | return #[]
  -- let res := ts.findSome? fun
  --   | .node (.ofCustomInfo { stx, value }) _ =>
  --     return (stx, (← value.get? (GenLeanVCThmsOutput)).res)
  --   | _ => none
  let out := customNodeFromTrees ts
  let some (stx, out) := out | return #[]
  let doc ← readDoc
  -- No action if the theorem text is already in the file.
  if out.text.isEmpty then
    return #[]
  let eager := {
    title := "Update #verify with output"
    kind? := "quickfix"
    edit? := .none,
    isPreferred? := true
  }
  pure #[{
    eager
    lazy? := some do
      let some start := stx.getPos? | return eager
      -- let some tail := stx.getTailPos? | return eager
      let newText := s!"{out.text}"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, start⟩
          newText
        }
      }
  }]

---------------------------------------------------------------------
end Strata
