/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Interpreter
public import Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.Interpreter
public import Strata.DL.Imperative.InterpreterTypesProps

/-! # Monadic-interpreter soundness: evaluator well-formedness and typed stores

The monad-free definitions the monadic interpreter's soundness argument
(`InterpreterSoundGeneric.lean`) runs under:

* `FactoryWF`: evaluator well-formedness at the factory of a run (Boolean negation, variable
  lookup, and agreement on stores that agree on an expression's free variables). No statement
  changes the factory, so a run has one factory and one `FactoryWF` hypothesis covers it;
* `InterpLangTyped`, `Config.storeTyped`: soundness of the engine's type checks, and typed stores.

Key theorems: `stepE_factory_eq` (an event step keeps the factory) and `Config.storeTyped_stepE`
(an event step preserves typed stores). -/

namespace Imperative

public section

variable {P : PureExpr}

/-- Evaluator well-formedness at the factory `f`: Boolean evaluation, variable evaluation and
    evaluation on stores agreeing on the free variables are all well-formed there. -/
@[expose] def FactoryWF [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] (f : P.Factory) :
    Prop :=
  WellFormedSemanticEvalBool (P := P) f ∧ WellFormedSemanticEvalVar (P := P) f ∧
    WellFormedSemanticEvalExprCongr (P := P) f

/-! ## Typed stores

The reference `.set` rules require the stored value to be typed, so engine soundness runs on
configurations with typed stores (`Config.storeTyped`), with the engine's type checks sound
against `HasVal.valueOfTy` (`InterpLangTyped`). -/

/-- The language's executable type checks (`InterpLang.ops.hasType`/`sameType`) are
    sound against the semantic typed-value predicate `HasVal.valueOfTy`. -/
class InterpLangTyped (P : PureExpr) [HasVal P] [InterpLang P] : Prop where
  ops_typed : (InterpLang.ops (P := P)).TypedSound InterpLang.rfactory InterpLang.denote

/-- Every store embedded in a configuration is typed (`StoreTyped`) under the
    factory it is read with; a `.block` frame's saved parent store is typed under
    the factory of the active environment. -/
@[expose] def Config.storeTyped {CmdT : Type} [HasVal P] : Config P CmdT → Prop
  | .stmt _ ρ => StoreTyped ρ.factory ρ.store
  | .stmts _ ρ => StoreTyped ρ.factory ρ.store
  | .terminal ρ => StoreTyped ρ.factory ρ.store
  | .exiting _ ρ => StoreTyped ρ.factory ρ.store
  | .block _ σp inner => StoreTyped inner.getEnv.factory σp ∧ Config.storeTyped inner
  | .seq inner _ => Config.storeTyped inner

/-- A reference event step keeps the factory of the configuration. -/
theorem stepE_factory_eq {CmdT : Type} {EventT : Type _} [HasBool P] [HasBoolOps P]
    {EvalCmd : EvalCmdParamE P CmdT EventT} {c c' : Config P CmdT} {evs : List EventT}
    (hstep : StepStmtE P EvalCmd c evs c') : c.getEnv.factory = c'.getEnv.factory := by
  induction hstep with
  | step_seq_inner _ ih => simpa [Config.getEnv] using ih
  | step_block_body _ ih => simpa [Config.getEnv] using ih
  | _ => simp [Config.getEnv]

/-- When every command evaluation keeps a typed store typed, one reference event step keeps
    every store of the configuration typed under its factory (`Config.storeTyped`). -/
theorem Config.storeTyped_stepE {CmdT : Type} {EventT : Type _} [HasBool P] [HasBoolOps P]
    {EvalCmd : EvalCmdParamE P CmdT EventT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT},
      EvalCmd f σ c σ' emitted → StoreTyped f σ → StoreTyped f σ')
    {c c' : Config P CmdT} {evs : List EventT}
    (hstep : StepStmtE P EvalCmd c evs c')
    (h : Config.storeTyped (P := P) c) : Config.storeTyped (P := P) c' := by
  induction hstep with
  | step_block_body hs ih =>
    exact ⟨stepE_factory_eq hs ▸ h.1, ih h.2⟩
  | _ => grind [Config.storeTyped, StoreTyped.projectStore, Config.getEnv]

end -- public section

end Imperative
