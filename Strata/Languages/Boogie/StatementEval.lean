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



import Strata.Languages.Boogie.Statement
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.OldExpressions
import Strata.Languages.Boogie.Env
import Strata.Languages.Boogie.CmdEval

---------------------------------------------------------------------

namespace Boogie

namespace Statement

open Std (ToFormat Format format)
open Lambda

---------------------------------------------------------------------

inductive CondType where
  | Requires
  | Ensures

instance : ToString CondType where
  toString c := match c with
  | .Requires => "Requires"
  | .Ensures => "Ensures"

/--
Helper function to create proof obligations and path conditions originating from
a `.call` statement.
-/
def callConditions (proc : Procedure)
                   (condType : CondType)
                   (conditions : Map String Procedure.Check)
                   (subst :  Map (Lambda.IdentT BoogieIdent) Expression.Expr) :
                   Map String Procedure.Check :=
  let names := List.map
               (fun k => s!"<Origin:{proc.header.name.2}_{condType}>{k}")
               conditions.keys
  let exprs := List.map
                (fun p =>
                  List.foldl
                    (fun c (x, v) =>
                      { expr := LExpr.substFvar c.expr x.fst v ,
                        attr := c.attr})
                    p subst)
                conditions.values
  List.zip names exprs

/--
Evaluate a procedure call `lhs := pname(args)`.
-/
-- (FIXME) Clean this code up.
def Command.evalCall (E : Env) (old_var_subst : SubstMap)
  (lhs : List Expression.Ident) (pname : String) (args : List Expression.Expr) (md : Imperative.MetaData Expression) :
  Command × Env :=
  -- Procedures in Boogie have a `modifies` clause that contain global variables that
  -- can be modified by the procedure. Also, the procedure's post-conditions can
  -- contain `old <var>` expressions, which refer to the value of
  -- `<var>` before the execution of the procedure (i.e., pre-state). See also
  -- `OldExpressions.lean`.
  --
  -- We apply some transformations to take these into account for the `call`
  -- statement. These are noted in comments below.
  -- We also require that all well-formed procedures identifiers to have a global scope
  -- This should be enforced by the type checker
  match Program.Procedure.find? E.program pname with
  | some proc =>
    -- Create a mapping from the formals to the evaluated actuals.
    let args' := List.map (fun a => E.exprEval (OldExpressions.substsOld old_var_subst a)) args
    let formal_tys := proc.header.inputs.keys.map (fun k => ((k, none) : (Lambda.IdentT BoogieIdent)))
    let formal_arg_subst := List.zip formal_tys args'
    -- Generate fresh variables for the LHS, and then create a mapping
    -- from the procedure's return variables to these LHS fresh
    -- variables.
    let lhs_tys :=
      lhs.map
      (fun l => (E.exprEnv.state.findD l (none, .fvar l none)).fst)
    let lhs_typed := lhs.zip lhs_tys
    let (lhs_fvars, E) := E.genFVars lhs_typed
    let return_tys := proc.header.outputs.keys.map (fun k => ((k, none) : (Lambda.IdentT BoogieIdent)))
    let return_lhs_subst := List.zip return_tys lhs_fvars
    -- The LHS fresh variables reflect the values of these variables
    -- in the post-call state.
    let lhs_post_subst := List.zip lhs_typed lhs_fvars
    -- Create a mapping from global variables to their current values
    -- (i.e., just before this call site). We will substitute all
    -- `old(v)` expressions in `proc`'s postconditions using this map.
    let current_globals_values := E.exprEnv.state.oldest.map (fun (id, _, e) => (id, e))
    let formal_arg_subst' := formal_arg_subst.map (fun ((i, _), e) => (i, e))
    let return_lhs_subst' := return_lhs_subst.map (fun ((i, _), e) => (i, e))
    let postcond_subst := current_globals_values ++ formal_arg_subst' ++ return_lhs_subst'
    let postconditions := OldExpressions.substsOldInProcChecks postcond_subst proc.spec.postconditions
    -- Create a mapping from global variables in the `modifies` clause
    -- of `proc` to fresh variables. Similar to the LHS fresh variables, these
    -- reflect the post-call value of these globals.
    let modifies_tys :=
        proc.spec.modifies.map
        (fun l => (E.exprEnv.state.findD l (none, .fvar l none)).fst)
    let modifies_typed := proc.spec.modifies.zip modifies_tys
    let (globals_fvars, E) := E.genFVars modifies_typed
    let globals_post_subst := List.zip modifies_typed globals_fvars
    let post_subst := globals_post_subst ++ lhs_post_subst
    -- Create proof obligations to ensure that the actuals and global
    -- variables in the modifies clause satisfy the procedure's
    -- preconditions.
    let subst := formal_arg_subst ++ return_lhs_subst ++ globals_post_subst
    let preconditions :=
        callConditions proc .Requires proc.spec.preconditions subst
    let preconditions := preconditions.map
                            (fun (l, e) => (toString l, Procedure.Check.mk (E.exprEval e.expr) e.attr))
    -- A free precondition is not checked at call sites, which is
    -- accounted for by `ProofObligations.create` below.
    let deferred_pre := ProofObligations.create E.pathConditions preconditions
    let E := { E with deferred := E.deferred ++ deferred_pre }
    -- If the preconditions hold, then the postconditions are
    -- guaranteed to hold.
    let postconditions :=
        callConditions proc .Ensures postconditions subst
    -- (TODO): Annotate "free" postconditions for record-keeping.
    let postconditions := (postconditions.keys.map toString).zip (Procedure.Spec.getCheckExprs postconditions)
    let E := { E with pathConditions := (E.pathConditions.addInNewest postconditions)}
    -- Update the LHS and global variables to reflect the post-call state.
    let post_vars_mdata := post_subst.map
                              (fun ((old, _), new) =>
                                Imperative.MetaDataElem.mk (.var old) (.expr new))
    let md' := md ++ post_vars_mdata.toArray
    let c' := CmdExt.call lhs pname args md'
    let E := E.addToContext post_subst
    (c', E)
  | _ =>
    let c' := CmdExt.call lhs pname args md
    let E := { E with error := some (.Misc f!"Procedure {pname} not found!") }
    (c', E)

def Command.eval (E : Env) (old_var_subst : SubstMap) (c : Command) : Command × Env :=
  match c with
  | .cmd c =>
    let (c, E) := Imperative.Cmd.eval { E with substMap := old_var_subst } c
    (.cmd c, E)
  | .call lhs pname args md =>
    Command.evalCall E old_var_subst lhs pname args md

---------------------------------------------------------------------

abbrev StmtsStack := List Statements

def StmtsStack.push (stk : StmtsStack) (ss : Statements) : StmtsStack :=
  let ss := Statements.eraseTypes ss
  ss :: stk

def StmtsStack.pop (stk : StmtsStack) : StmtsStack :=
  match stk with | [] => [] | _ :: rst => rst

def StmtsStack.top (stk : StmtsStack) : Statements :=
  match stk with | [] => [] | top :: _ => top

def StmtsStack.appendToTop (stk : StmtsStack) (ss : Statements) : StmtsStack :=
  let top := stk.top
  let stk := stk.pop
  let ss := Statements.eraseTypes ss
  (top ++ ss) :: stk

/--
A new environment with an optional next label to execute and transformed
statements (i.e., statements that have already been evaluated).
-/
structure EnvWithNext where
  env  : Env
  nextLabel : Option String := .none
  stk : StmtsStack := []

/--
Drop statements up to the given label, and indicate whether goto
needs to propagate up.
-/
def processGoto : Statements → Option String → (Statements × Option String)
| rest, .none => (rest, .none)
| rest, .some l =>
  match rest.dropWhile (fun s => !s.hasLabel l) with
  | [] => ([], .some l) -- Not found, so propagate goto
  | (rest') => (rest', .none) -- Found, so we're done

def evalAux (E : Env) (old_var_subst : SubstMap) (ss : Statements) (optLabel : Option String) :
  List EnvWithNext :=
  open LTy.Syntax in
  go (Imperative.Stmts.sizeOf ss) (EnvWithNext.mk E .none []) ss optLabel
  where go (steps : Nat) (Ewn : EnvWithNext)
           (ss : Statements) (optLabel : Option String) :
    List EnvWithNext :=
  match steps, Ewn.env.error with
  | _, some _ => [{Ewn with nextLabel := .none}]
  | 0, none => [{Ewn with env := { Ewn.env with error := some .OutOfFuel}, nextLabel := .none}]
  | steps' + 1, none =>
    let go' := go steps'
    match processGoto ss optLabel with
    | ([], .none) => [{ Ewn with nextLabel := .none }]
    | (_, .some l) => [{ Ewn with nextLabel := .some l }] -- Implies statement list is empty
    | (s :: rest, .none) =>
      let EAndNexts : List EnvWithNext :=
        match s with

          | .cmd c =>
            let (c', E) := Command.eval Ewn.env old_var_subst c
            [{ Ewn with stk := Ewn.stk.appendToTop [(Imperative.Stmt.cmd c')],
                        env := E,
                        nextLabel := .none }]

          | .block label { ss } md =>
            let orig_stk := Ewn.stk
            let Ewn := { Ewn with env := Ewn.env.pushEmptyScope,
                                  stk := orig_stk.push [] }
            let Ewns := go' Ewn ss .none -- Not allowed to jump into a block
            let Ewns := Ewns.map
                            (fun (ewn : EnvWithNext) =>
                                 { ewn with env := ewn.env.popScope,
                                            stk :=
                                              let ss' := ewn.stk.top
                                              let s' := Imperative.Stmt.block label { ss := ss' } md
                                              orig_stk.appendToTop [s'] })
            Ewns

          | .ite cond { ss := then_ss } { ss := else_ss } md =>
            let orig_stk := Ewn.stk
            let Ewn := { Ewn with stk := orig_stk.push [] }
            let cond' := Ewn.env.exprEval cond
            match cond' with
            | .const "true" _ =>
              let Ewns := go' Ewn then_ss .none -- Not allowed to jump into a block
              let Ewns := Ewns.map
                              (fun (ewn : EnvWithNext) =>
                                   let ss' := ewn.stk.top
                                   let s' := Imperative.Stmt.ite cond' { ss := ss' } { ss := [] } md
                                   { ewn with stk := orig_stk.appendToTop [s']})
              Ewns
            | .const "false" _ =>
              let Ewns := go' Ewn else_ss .none -- Not allowed to jump into a block
              let Ewns := Ewns.map
                              (fun (ewn : EnvWithNext) =>
                                   let ss' := ewn.stk.top
                                   let s' := Imperative.Stmt.ite cond' { ss := [] } { ss := ss' } md
                                   { ewn with stk := orig_stk.appendToTop [s']})
              Ewns
            | _ =>
              let Ewn := { Ewn with env := Ewn.env.pushEmptyScope }
              let label_true := toString (f!"<label_ite_cond_true: {cond.eraseTypes}>")
              let label_false := toString (f!"<label_ite_cond_false: !{cond.eraseTypes}>")
              let path_conds_true := Ewn.env.pathConditions.push [(label_true, cond')]
              let path_conds_false := Ewn.env.pathConditions.push
                                        [(label_false, (.ite cond' LExpr.false LExpr.true))]
              let Ewns_t := go' {Ewn with env := {Ewn.env with pathConditions := path_conds_true}} then_ss .none
              let Ewns_f := go' {Ewn with env := {Ewn.env with pathConditions := path_conds_false}} else_ss .none
              match Ewns_t, Ewns_f with
                -- Special case: if there's only one result from each path,
                -- with no next label, we can merge both states into one.
              | [{ stk := stk_t, env := E_t, nextLabel := .none}],
                [{ stk := stk_f, env := E_f, nextLabel := .none}] =>
                let s' := Imperative.Stmt.ite cond' { ss := stk_t.top } { ss := stk_f.top } md
                [EnvWithNext.mk (Env.merge cond' E_t E_f).popScope
                                .none
                                (orig_stk.appendToTop [s'])]
              | _, _ =>
                let Ewns_t := Ewns_t.map
                                  (fun (ewn : EnvWithNext) =>
                                    let s' := Imperative.Stmt.ite LExpr.true { ss := ewn.stk.top } { ss := [] } md
                                    { ewn with env := ewn.env.popScope,
                                               stk := orig_stk.appendToTop [s']})
                let Ewns_f := Ewns_f.map
                                  (fun (ewn : EnvWithNext) =>
                                    let s' := Imperative.Stmt.ite LExpr.false { ss := [] } { ss := ewn.stk.top } md
                                    { ewn with env := ewn.env.popScope,
                                               stk := orig_stk.appendToTop [s']})
                Ewns_t ++ Ewns_f

          | .loop _ _ _ _ _ =>
            panic! "Cannot evaluate `loop` statement. Please transform your program to eleminate loops before calling Boogie.Statement.evalAux"

          | .goto l md => [{ Ewn with stk := Ewn.stk.appendToTop [.goto l md], nextLabel := (some l)}]

      List.flatMap (fun (ewn : EnvWithNext) => go' ewn rest ewn.nextLabel) EAndNexts

def gotoToError : EnvWithNext → Statements × Env
  | { stk, env, nextLabel := .none } => (stk.flatten, env)
  | { stk, env, nextLabel := .some l } => (stk.flatten, { env with error := some (.LabelNotExists l) })

/--
Partial evaluator for statements yielding a list of environments and transformed
statements.

The argument `old_var_subst` below is a substitution map from global variables
to their pre-state value in the enclosing procedure of `ss`.
-/
def eval (E : Env) (old_var_subst : SubstMap) (ss : Statements) : List (Statements × Env) :=
  (evalAux E old_var_subst ss .none).map gotoToError

/--
Partial evaluator for statements yielding one environment and transformed
statements.
-/
def evalOne (E : Env) (old_var_subst : SubstMap) (ss : Statements) : Statements × Env :=
  match eval E old_var_subst ss with
  | [(ss', E')] => (ss', E')
  | _ => (ss, { E with error := some (.Misc "More than one result environment") })

end Statement
end Boogie

---------------------------------------------------------------------
