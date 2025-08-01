/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.DL.Imperative.DDMTranslate
import StrataTest.DL.Imperative.SMTEncoder
import Strata.DL.Imperative.SMTUtils

---------------------------------------------------------------------
namespace Arith
open Std (ToFormat Format format)

/-! ## Verifier for `ArithPrograms`

Here, we build an end-to-end verifier for `ArithPrograms`. We hook up the DDM
translator with the type checker + partial evaluator, followed by the SMT
encoder. We then write some basic functions to invoke an SMT solver on every
verification condition.
-/

open Strata.SMT in
def typedVarToSMT (v : String) (ty : Ty) : Except Format (String × Strata.SMT.TermType) := do
  let ty' ← toSMTType ty
  return (v, ty')

def verify (smtsolver : String) (cmds : Commands) (verbose : Bool) :
  EIO Format (Imperative.VCResults Arith.PureExpr) := do
  match typeCheckAndPartialEval cmds with
  | .error err =>
    .error s!"[Strata.Arith.verify] Error during evaluation!\n\
              {format err}\n\n\
              Evaluated program: {format cmds}\n\n"
  | .ok (cmds, S) =>
    let mut results := (#[] : Imperative.VCResults Arith.PureExpr)
    for obligation in S.deferred do
      dbg_trace f!"{obligation}"
      let maybeTerms := Arith.ProofObligation.toSMTTerms S.env obligation
      match maybeTerms with
      | .error err =>
        let msg := s!"[Strata.Arith.verify] SMT Encoding error for obligation {format obligation.label}: \n\
                     {err}\n\n\
                     Evaluated program: {format cmds}\n\n"
        let _ ← dbg_trace msg
        results := results.push { obligation, result := .err msg }
        break
      | .ok terms =>
        let ans ←
            IO.toEIO
              (fun e => f!"{e}")
              (@Imperative.dischargeObligation Arith.PureExpr _
               encodeArithToSMTTerms typedVarToSMT
               -- (FIXME)
               ((Arith.Eval.ProofObligation.freeVars obligation).map (fun v => (v, Arith.Ty.Num)))
                smtsolver (Imperative.smt2_filename obligation.label)
                terms)
        match ans with
        | .ok (result, estate) =>
           results := results.push { obligation, result, estate }
           if result ≠ .unsat then
            let prog := f!"\n\nEvaluated program:\n{format cmds}"
            dbg_trace f!"\n\nObligation {obligation.label}: could not be proved!\
                         \n\nResult: {result}\
                         {if verbose then prog else ""}"
            break
        | .error e =>
           results := results.push { obligation, result := .err (toString e) }
           let prog := f!"\n\nEvaluated program:\n{format cmds}"
           dbg_trace f!"\n\nObligation {obligation.label}: solver error!\
                        \n\nError: {e}\
                        {if verbose then prog else ""}"
           break
    return results


end Arith
---------------------------------------------------------------------

namespace Strata
namespace ArithPrograms

def verify (smtsolver : String) (env : Environment)
    (verbose : Bool := false) : IO (Imperative.VCResults Arith.PureExpr) := do
  let (program, errors) := ArithPrograms.TransM.run (ArithPrograms.translateProgram env.commands)
  if errors.isEmpty then
    EIO.toIO (fun f => IO.Error.userError (toString f))
                (Arith.verify smtsolver program verbose)
  else
    let errors := Std.Format.joinSep errors.toList "{Format.line}"
    panic! s!"DDM Transform Error: {errors}"

end ArithPrograms
end Strata

---------------------------------------------------------------------
