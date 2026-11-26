/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.Verifier
meta import Strata.Languages.Core.Typing.Soundness.Core
meta import Strata.Transform.CallElim
meta import Strata.Transform.ProcedureInlining
meta import Strata.Transform.LoopElim

/-! # The verification pipeline's type check

Programs built as abstract syntax, run through the verifier and its program transforms. -/

meta section

open Core Lambda

namespace VerifierPipelineTests

private def md : Imperative.MetaData Expression := #[]

private def ident (n : String) : Expression.Ident := ⟨n, ()⟩

private def intConst (i : Int) : Expression.Expr := .const Core.coreLoc (.intConst i)

/-- A procedure with the given signature, preconditions and structured body. -/
private def proc (name : String) (body : List Statement)
    (typeArgs : List String := []) (inputs : @Lambda.LMonoTySignature Unit := [])
    (outputs : @Lambda.LMonoTySignature Unit := [])
    (pre : List Expression.Expr := []) (post : List Expression.Expr := []) : Decl :=
  .proc {
    header := { name := ident name, typeArgs, inputs, outputs }
    spec := {
      preconditions := pre.zipIdx.map fun (e, i) => (s!"{name}_requires_{i}", { expr := e })
      postconditions := post.zipIdx.map fun (e, i) => (s!"{name}_ensures_{i}", { expr := e }) }
    body := .structured body false } md

/-- The verifier's results for `p` under `options`. -/
private def verify (p : Program) (options : VerifyOptions := .quiet) : IO Core.VCResults :=
  (Strata.Core.verifyProgram p options).toIO IO.userError

/-- `p` after the phases `phases`, or the error. -/
private def transformed (p : Program) (phases : List PipelinePhase) : IO Unit := do
  match ← (runTransforms p phases).toBaseIO with
  | .ok (q, _) => IO.println (toString q)
  | .error e => IO.println s!"error: {e.message}"

/-! ## The whole program is checked before the procedure filter

`Bad` initializes an integer variable with a boolean, and is not among the procedures to
verify; the run is refused all the same. -/

private def goodProc : Decl := proc "Good" [Statement.assert "good" (.true Core.coreLoc) md]

private def badProc : Decl :=
  proc "Bad" [Statement.init (ident "x") (.forAll [] .int) (.det (.true Core.coreLoc)) md]

private def onlyGood : VerifyOptions :=
  { VerifyOptions.quiet with proceduresToVerify := some ["Good"] }

/--
error: ❌ Type checking error.
Procedure 'Bad': Impossible to unify int with bool.
-/
#guard_msgs in
#eval verify { decls := [goodProc, badProc] } onlyGood

/--
info:
Obligation: good
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify { decls := [goodProc] } onlyGood

/-! ## A safe accessor of a two-constructor datatype

`Inner..x(m)` requires `m` to be an `Inner_Cons`; both that precondition and the assertion
reach the solver, which refutes them. -/

private def innerType : LDatatype Unit :=
  { name := "Inner", typeArgs := []
    constrs := [
      { name := ident "Inner_Cons", args := [(ident "x", .int)],
        testerName := "Inner..isInner_Cons" },
      { name := ident "Inner_Nil", args := [], testerName := "Inner..isInner_Nil" }]
    constrs_ne := rfl }

private def accessor : Program :=
  { decls := [
      .type (.data [innerType]) md,
      proc "P" (inputs := [(ident "m", .tcons "Inner" [])])
        [Statement.assert "x_zero"
          (.eq Core.coreLoc (.app Core.coreLoc (.op Core.coreLoc (ident "Inner..x") none)
                             (.fvar Core.coreLoc (ident "m") none))
            (intConst 0)) md]] }

/--
info:
Obligation: assert_x_zero_calls_Inner..x_0
Property: assert
Result: ❌ fail

Obligation: x_zero
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify accessor

/-! ## A callee type parameter that a call does not determine

`q<a>` has no argument of type `a`, so a call to it leaves `a` open. The checker rejects the
caller, because the call's stored type argument is not one of its type parameters. -/

private def reflexive : Expression.Expr :=
  .quant Core.coreLoc .all "y" (some (.ftvar "a")) (LExpr.noTrigger Core.coreLoc)
      (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))

private def undetermined : Program :=
  { decls := [
      proc "q" [] (typeArgs := ["a"]) (pre := [reflexive]),
      proc "caller" [Statement.call "q" none [] md, Statement.call "q" none [] md]] }

private def checkThenCallElim : List PipelinePhase :=
  [ProgramFact.assertPhase .noCFGBodies, typeCheckPipelinePhase .quiet, callElimPipelinePhase]

/--
info: error: ❌ Type checking error.
Procedure 'caller': the call to 'q' does not determine one of its type
parameters
-/
#guard_msgs (whitespace := lax) in
#eval transformed undetermined checkThenCallElim

/--
error: ❌ Type checking error.
Procedure 'caller': the call to 'q' does not determine one of its type
parameters
-/
#guard_msgs (whitespace := lax) in
#eval verify undetermined

/-! ## A function precondition at the caller's own type parameter

`g<a>()` requires `forall y : a :: y == y`, and `p<a>` calls it at its own `a`. After the check
the call's annotation is `g`'s declared type, so the precondition is instantiated at `a`, which
then becomes an opaque type of `p`; the program verifies. -/

private def preconditioned : Program :=
  { decls := [
      .func { name := ident "g", typeArgs := ["a"], inputs := [], output := .ftvar "a",
              preconditions := [⟨reflexive, default⟩] } md,
      proc "p" (typeArgs := ["a"])
        [Statement.init (ident "z") (.forAll [] (.ftvar "a"))
          (.det (.op Core.coreLoc (ident "g") none)) md]] }

/--
info:
Obligation: init_calls_g_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify preconditioned

/-! ## Call elimination after the check

The `transform` command's passes, `typeCheck` and then `callElim`, on a call to a polymorphic
identity procedure: the contract appears at the call's instance `int`. -/

private def identity : Program :=
  { decls := [
      proc "id" [] (typeArgs := ["a"]) (inputs := [(ident "x", .ftvar "a")])
        (outputs := [(ident "r", .ftvar "a")])
        (post := [.eq Core.coreLoc (.fvar Core.coreLoc (ident "r") none)
                  (.fvar Core.coreLoc (ident "x") none)]),
      proc "caller"
        [Statement.init (ident "z") (.forAll [] .int) .nondet md,
         Statement.call "id" none [.inArg (intConst 5), .outArg (ident "z")] md]] }

/--
info: program Core;

procedure id<a> (x : a, out r : a)
spec {
  ensures [id_ensures_0]: r == x;
  } {
  
};
procedure caller ()
{
  var z : int;
  var tmp_arg_0 : int := 5;
  var tmp_z_1 : int := z;
  havoc z;
  assume [$__callElimAssume_id_ensures_0_2]: z == tmp_arg_0;
};
-/
#guard_msgs in
#eval transformed identity
  [Strata.Core.passTypeCheck VerifyOptions.quiet, Strata.Core.passCallElim]

/-! ## Every `exit` stays inside a block that catches it

The callee exits its labeled block from inside a loop; the caller calls it from a loop inside its
own labeled block, and exits that block. The fact `exitsCovered` holds before and after each
transform that rewrites loops, calls or procedures. -/

/-- A loop that may exit `label` after the statements `pre`. -/
private def exitingLoop (label : String) (pre : List Statement := []) : Statement :=
  .loop .nondet none [] (pre ++ [.ite .nondet [.exit label md] [] md]) md

/-- A callee that exits its block from inside a loop, called from a loop in the caller's block. -/
private def exiting : Program :=
  { decls := [
      proc "callee" [.block "b" [exitingLoop "b"] md],
      proc "caller" [.block "c" [exitingLoop "c" [Statement.call "callee" none [] md]] md]] }

/-- The phase that asserts every `exit` is inside a block that catches it. -/
private def covered : PipelinePhase := ProgramFact.assertPhase .exitsCovered

/-- Type checking followed by the exit-coverage assertion. -/
private def checked : List PipelinePhase := [typeCheckPipelinePhase .quiet, covered]

/--
info: program Core;

procedure callee ()
{
  b: {
    if * {
      $__loopElim_arbitrary_iter_facts_loop_0: {
        $__loopElim_havoc_loop_0: {
          
        }
        assume [$__loopElimAssume_guard_loop_0]: true;
        if * {
          exit b;
        }
      }
      $__loopElim_havoc_loop_0: {
        
      }
      assume [$__loopElimAssume_not_guard_loop_0]: true;
    }
  }
};
procedure caller ()
{
  c: {
    if * {
      $__loopElim_arbitrary_iter_facts_loop_1: {
        $__loopElim_havoc_loop_1: {
          
        }
        assume [$__loopElimAssume_guard_loop_1]: true;
        $__inline1_callee$inlined: {
          $__inline1_b: {
            if * {
              $__loopElim_arbitrary_iter_facts_loop_2: {
                $__loopElim_havoc_loop_2: {
                  
                }
                assume [$__loopElimAssume_guard_loop_2]: true;
                if * {
                  exit $__inline1_b;
                }
              }
              $__loopElim_havoc_loop_2: {
                
              }
              assume [$__loopElimAssume_not_guard_loop_2]: true;
            }
          }
        }
        if * {
          exit c;
        }
      }
      $__loopElim_havoc_loop_1: {
        
      }
      assume [$__loopElimAssume_not_guard_loop_1]: true;
    }
  }
};
-/
#guard_msgs in
#eval transformed exiting (checked ++ [procedureInliningPipelinePhase {}, covered,
  loopElimPipelinePhase, covered])

/--
info: program Core;

procedure callee ()
{
  b: {
    if * {
      $__loopElim_arbitrary_iter_facts_loop_0: {
        $__loopElim_havoc_loop_0: {
          
        }
        assume [$__loopElimAssume_guard_loop_0]: true;
        if * {
          exit b;
        }
      }
      $__loopElim_havoc_loop_0: {
        
      }
      assume [$__loopElimAssume_not_guard_loop_0]: true;
    }
  }
};
procedure caller ()
{
  c: {
    if * {
      $__loopElim_arbitrary_iter_facts_loop_1: {
        $__loopElim_havoc_loop_1: {
          
        }
        assume [$__loopElimAssume_guard_loop_1]: true;
        if * {
          exit c;
        }
      }
      $__loopElim_havoc_loop_1: {
        
      }
      assume [$__loopElimAssume_not_guard_loop_1]: true;
    }
  }
};
-/
#guard_msgs in
#eval transformed exiting (checked ++ [Strata.Core.passPrecondElim, covered,
  Strata.Core.passTermCheck, covered, Strata.Core.passGenOpaqueTypeParams, covered,
  Strata.Core.passFilterProcedures ["caller"], covered, callElimPipelinePhase, covered,
  loopElimPipelinePhase, covered])

/-- A body that exits a label no enclosing block declares. -/
private def undeclaredExit : Program :=
  { decls := [proc "p" [.block "b" [.exit "other" md] md]] }

/--
info: error: ❌ Type checking error.
Procedure 'p': exit other: exit label "other" does not match any enclosing block.
-/
#guard_msgs in
#eval transformed undeclaredExit [typeCheckPipelinePhase .quiet, covered]

/-! ## The type check establishes well-formed calls

It requires nothing and establishes `wellFormedCalls`: its output's calls are well formed, CFG
bodies included. -/

#guard (typeCheckPipelinePhase .quiet).requires.facts == []
#guard (typeCheckPipelinePhase .quiet).establishes.facts.contains .wellFormedCalls
#guard (typeCheckPipelinePhase .quiet).establishes.facts.contains .typeAnnotated

-- On the identity program, the checker's output passes the well-formed-calls check.
#guard match Core.typeCheck .quiet identity with
  | .ok p => (ProgramFact.wellFormedCalls.check?.get rfl) p
  | .error _ => false

/-- The checker's output has only well-formed calls. -/
example (p p' : Program) (h : Core.typeCheck .quiet p = .ok p') : p'.callsWellFormed :=
  typeCheck_callsWellFormed .quiet p p' none Lambda.Factory.default h

end VerifierPipelineTests

end -- meta section
