/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.DL.Imperative.SMTUtils
public meta import Strata.Languages.Core.SMTEncoder

/-! # Feeding a captured solver answer to `solverResult`

Model tests read a solver answer (a `check-sat` verdict and its `get-value` response) with
`solverResult`, as the verifier does, but without running a solver: the answer is given as
the solver's standard output. -/

meta section

public section

namespace Strata.SMT.ModelTestHarness

open Imperative.SMT

/-- The SMT encoding of a variable or constant: its own name (types play no role in
    reading a model back). -/
def intVar (x : Core.Expression.Ident) (_ : Core.Expression.Ty) :
    Except Std.Format (String × Strata.SMT.TermType) :=
  .ok (x.name, .int)

/-- An encoder state that declares `names` as integer variables. -/
def encoderWith (names : List String) : Strata.SMT.EncoderState :=
  { Strata.SMT.EncoderState.init with
    functions := names.foldl (init := {}) fun m n => m.insert ⟨n, [], .int⟩ n }

/-- The `solverResult` of the cvc5 answer `stdout` to a query on `vars`: the satisfiability
    check (`A ∧ Q`) when `cover` holds, the validity check (`A ∧ ¬Q`) otherwise. -/
def readAnswer (vars : List Core.Expression.TypedIdent) (stdout : String)
    (cover : Bool := false) :
    IO (Except SolverError (Result Core.Expression.Ident × Result Core.Expression.Ident)) :=
  solverResult intVar vars { exitCode := 0, stdout, stderr := "" }
    (encoderWith (vars.map (·.1.name))) "cvc5" cover !cover

end Strata.SMT.ModelTestHarness

end

end
