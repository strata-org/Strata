/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Boogie.Options
import Strata.Languages.Boogie.ProgramEval
import Strata.Languages.Boogie.ProgramType

---------------------------------------------------------------------

namespace Boogie

/-!
## Differences between Boogie and Strata.Boogie

1. Local variables can shadow globals in Boogie, but the typechecker disallows
   that in Strata.Boogie.

2. Unlike Boogie, Strata.Boogie is sensitive to global declaration order. E.g.,
   a global variable must be declared before it can be used in a procedure.

3. Strata.Boogie does not (yet) support polymorphism.

4. Strata.Boogie does not (yet) support arbitrary gotos. All gotos must
   currently be to labels later in the program.

5. Strata.Boogie does not support `where` clauses and `unique` constants,
   requiring a tool like `BoogieToStrata` to desugar them.

6. Strata.Boogie does not support algebraic data types or regular expression
   types.
-/

def typeCheck (options : Options) (program : Program)
    (moreFns : @Lambda.Factory BoogieLParams := Lambda.Factory.default) :
    Except Std.Format Program := do
  let T := Lambda.TEnv.default
  let factory ← Boogie.Factory.addFactory moreFns
  let C := { Lambda.LContext.default with
                functions := factory,
                knownTypes := Boogie.KnownTypes }
  let (program, _T) ← Program.typeCheck C T program
  -- dbg_trace f!"[Strata.Boogie] Type variables:\n{T.state.substInfo.subst.length}"
  -- dbg_trace f!"[Strata.Boogie] Annotated program:\n{program}"
  if options.verbose then dbg_trace f!"[Strata.Boogie] Type checking succeeded.\n"
  return program

def typeCheckAndPartialEval (options : Options) (program : Program)
    (moreFns : @Lambda.Factory BoogieLParams := Lambda.Factory.default) :
    Except Std.Format (List (Program × Env)) := do
  let program ← typeCheck options program moreFns
  -- Extract datatypes from program declarations and add to environment
  let datatypes := program.decls.filterMap fun decl =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let σ ← (Lambda.LState.init).addFactory Boogie.Factory
  let σ ← σ.addFactory moreFns
  let E := { Env.init with exprEnv := σ,
                           program := program }
  let E ← E.addDatatypes datatypes
  let pEs := Program.eval E
  if options.verbose then do
    dbg_trace f!"{Std.Format.line}VCs:"
    for (_p, E) in pEs do
      -- dbg_trace f!"Program: {p}"
      dbg_trace f!"{ProofObligations.eraseTypes E.deferred}"
  return pEs

instance : ToString (Program) where
  toString p := toString (Std.format p)

end Boogie

---------------------------------------------------------------------
