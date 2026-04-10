/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Interpreter
import Strata.Languages.Core.StatementSemantics

/-! # Soundness of the Core Interpreter

This module states and (partially) proves that the concrete interpreter
(`Interpreter.lean`) is sound with respect to the small-step operational
semantics (`StmtSemanticsSmallStep.lean`).

## Proof Architecture

1. **Store bridging** — relates `Core.Env` (scoped maps) to `SemanticStore`.
2. **Expression evaluation** — `LExpr.eval` is a valid `SemanticEval`.
3. **Command soundness** — `interpCmd` results satisfy `EvalCmd`.
4. **Statement soundness** — `interpStmt` results satisfy `StepStmtStar`.
5. **Block soundness** — `interpBlock` results satisfy `EvalStmtsSmall`.
-/

namespace Core

open Lambda Imperative
open Std (ToFormat Format format)

/-! ## Store Bridging -/

/-- Extract a `SemanticStore` from a `Core.Env` by flattening the scoped maps. -/
noncomputable def storeOf (E : Env) : CoreStore :=
  fun x => (E.exprEnv.state.find? x).map (·.snd)

/-- Extract a `SemanticEval` from a `Core.Env`. -/
noncomputable def evalOf (E : Env) : CoreEval :=
  fun _σ e => some (E.exprEval e)

/-- Build an `Imperative.Env` from a `Core.Env`. -/
noncomputable def impEnvOf (E : Env) : Imperative.Env Expression :=
  { store := storeOf E
    eval := evalOf E
    hasFailure := E.error.isSome }

/-! ## Expression Evaluation Agreement -/

theorem evalOf_eq (E : Env) (e : Expression.Expr) :
    evalOf E (storeOf E) e = some (E.exprEval e) := by
  simp [evalOf]

/-! ## Command Soundness

For each command case in `interpCmd`, the result satisfies `EvalCmd`.
-/

/-
Theorem: For all fuel, E, c, E', if interpCmd returns .normal E' for an
  Imperative command c, then EvalCmd holds between the corresponding stores.

Proof:
  By cases on c.

  Case (.init x ty (.det e) md):
    1. interpCmd evaluates e to v := E.exprEval e
       by definition of interpCmd
    2. evalOf E (storeOf E) e = some v
       by evalOf_eq
    3. insertVar E x ty v produces E' with (storeOf E') x = some v
       by definition of insertVar and Maps.insert
    4. InitState (storeOf E) x v (storeOf E') holds
       by 3 and definition of InitState [LEMMA - needs Maps.insert properties]
    5. done
       by EvalCmd.eval_init with 2 and 4

  Case (.init x ty .nondet md):
    1. interpCmd produces E' with x mapped to defaultValue ty
    2. InitState (storeOf E) x (defaultValue ty) (storeOf E') holds
       by same Maps.insert lemma
    3. done
       by EvalCmd.eval_init_unconstrained with 2

  Case (.set x (.det e) md):
    Similar to init, using UpdateState and eval_set.

  Case (.set x .nondet md):
    Similar, using eval_set_nondet.

  Case (.assert label e md):
    1. interpCmd evaluates e and checks denoteBool
    2. If denoteBool = some true:
       evalOf gives δ σ e = some (E.exprEval e)
       Need: E.exprEval e = HasBool.tt [LEMMA - denoteBool true ↔ value is tt]
       done by eval_assert_pass
    3. If denoteBool = some false:
       Similar, done by eval_assert_fail

  Case (.assume label e md):
    1. Only succeeds when denoteBool = some true
    2. done by eval_assume

  Case (.cover label e md):
    1. Returns E unchanged
    2. done by eval_cover
-/

theorem interp_sound_cmd (fuel : Nat) (E : Env) (c : Imperative.Cmd Expression)
    (E' : Env)
    (h : interpCmd (fuel + 1) E (.cmd c) = some (.normal E')) :
    ∃ σ' f,
      Imperative.EvalCmd (P := Expression) (evalOf E) (storeOf E) c σ' f ∧
      storeOf E' = σ' ∧
      E'.error.isSome = f := by
  sorry

/-! ## Auxiliary: Maps.insert satisfies InitState / UpdateState

These lemmas bridge the concrete map operations used by the interpreter
with the abstract store relations used by the relational semantics.
-/

/-
Lemma: Maps.insert on a key not in the store satisfies InitState.

Proof: By induction on the store structure.
  1. Maps.insert on a fresh key adds it to the newest scope
     by definition of Maps.insert
  2. storeOf of the result maps x to some v and preserves other keys
     by definition of Maps.find? and Map.insert
  3. This matches the InitState constructor requirements
     by definition of InitState
-/

theorem maps_insert_initState (E : Env) (x : Expression.Ident)
    (ty : Option LMonoTy) (v : Expression.Expr)
    (hfresh : E.exprEnv.state.find? x = none) :
    InitState Expression (storeOf E) x v
      (storeOf (E.insertInContext (x, ty) v)) := by
  sorry

/-
Lemma: Maps.insert on a key already in the store satisfies UpdateState.

Proof: Similar to above, but using UpdateState constructor.
-/

theorem maps_insert_updateState (E : Env) (x : Expression.Ident)
    (ty : Option LMonoTy) (v : Expression.Expr)
    (hexists : (E.exprEnv.state.find? x).isSome) :
    UpdateState Expression (storeOf E) x v
      (storeOf (E.insertInContext (x, ty) v)) := by
  sorry

/-
Lemma: denoteBool true implies the expression equals HasBool.tt.

Proof:
  1. denoteBool e = some true means e = .boolConst _ true
     by definition of denoteBool
  2. HasBool.tt for Core.Expression is .boolConst () true
     by definition of HasBool instance
  3. done
-/

theorem denoteBool_true_eq_tt (e : Expression.Expr)
    (h : LExpr.denoteBool e = some true) :
    e = HasBool.tt := by
  sorry -- Requires showing: denoteBool e = some true → e = .boolConst () true
         -- and .boolConst () true = HasBool.tt (up to metadata)

theorem denoteBool_false_eq_ff (e : Expression.Expr)
    (h : LExpr.denoteBool e = some false) :
    e = HasBool.ff := by
  sorry -- Symmetric to above

/-! ## Statement Soundness -/

/-
Theorem: If interpStmt returns .normal E', then the relational semantics
  can reach a terminal configuration with the corresponding store.

Proof: By cases on stmt, using interp_sound_cmd for commands and
  mutual induction with interp_sound_block for compound statements.

  Case (.cmd (.cmd c)):
    1. interpCmd returns .normal E'
       by hypothesis
    2. EvalCmd holds between storeOf E and storeOf E'
       by interp_sound_cmd
    3. StepStmt via step_cmd
    4. done
       by ReflTrans.single with 3

  Case (.block label stmts md):
    1. interpStmt pushes scope, calls interpBlock, pops scope
    2. By interp_sound_block: relational steps stmts to terminal
    3. Wrap with step_block → step_block_body* → step_block_done
    4. done

  Case (.ite (.det c) thenBr elseBr md):
    1. E.exprEval c reduces to a bool
    2. If true: step_ite_true, then interp_sound_block on thenBr
    3. If false: step_ite_false, then interp_sound_block on elseBr
    4. done

  Case (.loop (.det g) measure invs body md):
    By well-founded induction on fuel.
    1. E.exprEval g reduces to a bool
    2. If false: step_loop_exit; done
    3. If true:
       3.1. interp_sound_block on body gives ρ₁
       3.2. Recursive call on the loop with fuel-1 gives ρ'
       3.3. Relational: step_loop_enter steps to body ++ [loop]
       3.4. Compose body steps with recursive loop steps
       3.5. done

  Case (.exit label md):
    1. Returns .exiting, not .normal
    2. This case doesn't apply to the .normal conclusion
    3. done (vacuously)

  Case (.funcDecl decl md):
    1. step_funcDecl
    2. Need: evalOf agreement after factory extension [LEMMA]
    3. done

  Case (.typeDecl tc md):
    1. step_typeDecl; done
-/

-- The procedure lookup used by the relational semantics
noncomputable def procLookup (E : Env) : String → Option Procedure :=
  fun name => Program.Procedure.find? E.program ⟨name, ()⟩

-- Placeholder for the evaluator extension function
noncomputable def evalExtension : CoreEval → PureFunc Expression → CoreEval :=
  fun δ _decl => δ  -- simplified; real version would extend δ

theorem interp_sound_stmt (fuel : Nat) (E : Env) (stmt : Statement)
    (E' : Env)
    (h : interpStmt (fuel + 1) E stmt = some (.normal E')) :
    ∃ ρ' : Imperative.Env Expression,
      EvalStmtSmall Expression
        (EvalCommand (procLookup E) evalExtension)
        (EvalPureFunc evalExtension)
        (impEnvOf E) stmt ρ' ∧
      storeOf E' = ρ'.store := by
  sorry

/-! ## Block Soundness -/

/-
Theorem: If interpBlock returns .normal E', then the relational semantics
  can step the statement list to a terminal configuration.

Proof: By induction on stmts.

  Base case (stmts = []):
    1. interpBlock returns E unchanged
       by definition
    2. step_stmts_nil: (.stmts [] ρ) → (.terminal ρ)
    3. storeOf E = (impEnvOf E).store
       by definition
    4. done

  Inductive case (stmts = s :: rest):
    1. interpBlock calls interpStmt on s, getting outcome₁
    2. outcome₁ = .normal E₁ (otherwise short-circuits)
    3. interpBlock calls itself on rest with E₁, getting .normal E'
    4. By interp_sound_stmt: ∃ ρ₁, EvalStmtSmall ... (impEnvOf E) s ρ₁
    5. By IH: ∃ ρ', EvalStmtsSmall ... (impEnvOf E₁) rest ρ'
    6. Need: impEnvOf E₁ = ρ₁ [LEMMA - store agreement after stmt]
    7. Compose: step_stmts_cons → step_seq_inner* → step_seq_done → ...
    8. done
-/

theorem interp_sound_block (fuel : Nat) (E : Env) (stmts : Statements)
    (E' : Env)
    (h : interpBlock (fuel + 1) E stmts = some (.normal E')) :
    ∃ ρ' : Imperative.Env Expression,
      EvalStmtsSmall Expression
        (EvalCommand (procLookup E) evalExtension)
        (EvalPureFunc evalExtension)
        (impEnvOf E) stmts ρ' ∧
      storeOf E' = ρ'.store := by
  sorry

end Core
