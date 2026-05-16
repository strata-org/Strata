/-
  Standalone version of StructuredToUnstructuredCorrect.lean

  Contains all theorem statements and proofs from the original file with
  inlined dependencies (full definitions of stmtsToCFG, stmtsToBlocks, etc.).
  No imports beyond the Lean core library.
-/

-- ============================================================
-- Utility types
-- ============================================================

section Util

def ListMap (α : Type u) (β : Type v) := List (α × β)

namespace ListMap

def values {α : Type u} {β : Type v} (m : ListMap α β) : List β :=
  (m : List (α × β)).map Prod.snd

end ListMap

end Util

-- ============================================================
-- Relations
-- ============================================================

section Relations

def Relation (A : Type) := A → A → Prop

inductive ReflTrans {A : Type} (r : Relation A) : Relation A where
  | refl : ∀ x, ReflTrans r x x
  | step : ∀ x y z, r x y → ReflTrans r y z → ReflTrans r x z

theorem ReflTrans_Transitive {A : Type} (r : Relation A) :
    ∀ x y z, ReflTrans r x y → ReflTrans r y z → ReflTrans r x z := by
  intro x y z rxy
  induction rxy generalizing z with
  | refl => intro h; exact h
  | step x1 y1 z1 rxy1 _ IH =>
    intro rzz1
    exact ReflTrans.step _ y1 _ rxy1 (IH _ rzz1)

end Relations

-- ============================================================
-- StringGenState / LabelGen
-- ============================================================

section LabelGen

namespace Counter

structure CounterState where
  counter : Nat := 0
  generated : List Nat := []

def CounterState.emp : CounterState := { counter := 0, generated := [] }

def genCounter (σ : CounterState) : Nat × CounterState :=
  (σ.counter, { counter := σ.counter + 1, generated := σ.counter :: σ.generated })

end Counter

structure StringGenState where
  cs : Counter.CounterState
  generated : List (Nat × String)

instance : HasSubset StringGenState where
  Subset σ₁ σ₂ := σ₁.generated.unzip.2.Subset σ₂.generated.unzip.2

@[simp]
def StringGenState.emp : StringGenState := { cs := .emp, generated := [] }

def StringGenState.gen (pf : String) (σ : StringGenState) : String × StringGenState :=
  let (counter, cs) := Counter.genCounter σ.cs
  let newString : String := (pf ++ "_" ++ toString counter)
  let newState : StringGenState := { cs, generated := (counter, newString) :: σ.generated }
  (newString, newState)

abbrev StringGenM := StateM StringGenState

end LabelGen

-- ============================================================
-- TypeConstructor (stub)
-- ============================================================

structure TypeConstructor where
  name   : String
  params : List String := []

-- ============================================================
-- PureExpr and type classes
-- ============================================================

namespace Imperative

structure PureExpr : Type 1 where
  Ident       : Type
  EqIdent     : DecidableEq Ident
  Expr        : Type
  Ty          : Type
  ExprMetadata : Type
  TyEnv       : Type
  TyContext    : Type
  EvalEnv     : Type

abbrev PureExpr.TypedIdent (P : PureExpr) := P.Ident × P.Ty

class HasBool (P : PureExpr) where
  tt : P.Expr
  ff : P.Expr
  tt_is_not_ff : tt ≠ ff
  boolTy : P.Ty

class HasNot (P : PureExpr) extends HasBool P where
  not : P.Expr → P.Expr

class HasIntOrder (P : PureExpr) where
  eq    : P.Expr → P.Expr → P.Expr
  lt    : P.Expr → P.Expr → P.Expr
  zero  : P.Expr
  intTy : P.Ty

class HasIdent (P : PureExpr) where
  ident : String → P.Ident

class HasFvar (P : PureExpr) where
  mkFvar : P.Ident → P.Expr
  getFvar : P.Expr → Option P.Ident

class HasVal (P : PureExpr) where
  value : P.Expr → Prop

class HasSubstFvar (P : PureExpr) where
  substFvar  : P.Expr → P.Ident → P.Expr → P.Expr
  substFvars : P.Expr → List (P.Ident × P.Expr) → P.Expr

class HasVarsPure (P : PureExpr) (α : Type) where
  getVars : α → List P.Ident

-- ============================================================
-- Func / PureFunc
-- ============================================================

structure FuncPrecondition (ExprT : Type) (MetadataT : Type) where
  expr : ExprT
  md   : MetadataT

structure Func (IdentT : Type) (ExprT : Type) (TyT : Type) (MetadataT : Type) where
  name         : IdentT
  isRecursive  : Bool := false
  inputs       : ListMap IdentT TyT
  output       : TyT
  body         : Option ExprT := .none
  preconditions : List (FuncPrecondition ExprT MetadataT) := []

abbrev PureFunc (P : PureExpr) := Func P.Ident P.Expr P.Ty P.ExprMetadata

-- ============================================================
-- MetaData (minimal)
-- ============================================================

structure MetaDataElem (P : PureExpr) where
  fld   : String
  value : String

abbrev MetaData (P : PureExpr) := Array (MetaDataElem P)

def MetaData.empty {P : PureExpr} : MetaData P := #[]

-- ============================================================
-- ExprOrNondet
-- ============================================================

inductive ExprOrNondet (P : PureExpr) where
  | det (e : P.Expr)
  | nondet
  deriving Inhabited

-- ============================================================
-- Cmd
-- ============================================================

inductive Cmd (P : PureExpr) : Type where
  | init   (name : P.Ident) (ty : P.Ty) (e : ExprOrNondet P) (md : MetaData P)
  | set    (name : P.Ident) (e : ExprOrNondet P) (md : MetaData P)
  | assert (label : String) (b : P.Expr) (md : MetaData P)
  | assume (label : String) (b : P.Expr) (md : MetaData P)
  | cover  (label : String) (b : P.Expr) (md : MetaData P)

class HasPassiveCmds (P : PureExpr) (CmdT : Type) where
  assume : String → P.Expr → MetaData P → CmdT
  assert : String → P.Expr → MetaData P → CmdT

instance : HasPassiveCmds P (Cmd P) where
  assume l e md := .assume l e md
  assert l e md := .assert l e md

class HasInit (P : PureExpr) (CmdT : Type) where
  init : P.Ident → P.Ty → ExprOrNondet P → MetaData P → CmdT

instance : HasInit P (Cmd P) where
  init x ty e md := .init x ty e md

-- ============================================================
-- Stmt
-- ============================================================

inductive Stmt (P : PureExpr) (CmdT : Type) : Type where
  | cmd      (cmd : CmdT)
  | block    (label : String) (b : List (Stmt P CmdT)) (md : MetaData P)
  | ite      (cond : ExprOrNondet P) (thenb : List (Stmt P CmdT)) (elseb : List (Stmt P CmdT)) (md : MetaData P)
  | loop     (guard : ExprOrNondet P) (measure : Option P.Expr)
             (invariants : List (String × P.Expr))
             (body : List (Stmt P CmdT)) (md : MetaData P)
  | exit     (label : Option String) (md : MetaData P)
  | funcDecl (decl : PureFunc P) (md : MetaData P)
  | typeDecl (tc : TypeConstructor) (md : MetaData P)

-- exitsCoveredByBlocks
def Stmt.exitsCoveredByBlocks : List (Option String) → Stmt P CmdT → Prop
  | _, .cmd _ => True
  | labels, .block l ss _ => Block.exitsCoveredByBlocks (.some l :: labels) ss
  | labels, .ite _ tss ess _ => Block.exitsCoveredByBlocks labels tss ∧ Block.exitsCoveredByBlocks labels ess
  | labels, .loop _ _ _ body _ => Block.exitsCoveredByBlocks labels body
  | labels, .exit none _ => labels.length > 0
  | labels, .exit (some l) _ => .some l ∈ labels
  | _, .funcDecl _ _ => True
  | _, .typeDecl _ _ => True
where
  Block.exitsCoveredByBlocks : List (Option String) → List (Stmt P CmdT) → Prop
    | _, [] => True
    | labels, s :: ss => Stmt.exitsCoveredByBlocks labels s ∧ Block.exitsCoveredByBlocks labels ss

-- ============================================================
-- CmdSemantics
-- ============================================================

abbrev SemanticStore (P : PureExpr) := P.Ident → Option P.Expr
abbrev SemanticEval (P : PureExpr) := SemanticStore P → P.Expr → Option P.Expr

abbrev EvalCmdParam (P : PureExpr) (CmdT : Type) :=
  SemanticEval P → SemanticStore P → CmdT → SemanticStore P → Bool → Prop

def WellFormedSemanticEvalBool {P : PureExpr} [HasBool P] [HasNot P]
    (δ : SemanticEval P) : Prop :=
    ∀ σ e,
      (δ σ e = some HasBool.tt ↔ δ σ (HasNot.not e) = some HasBool.ff) ∧
      (δ σ e = some HasBool.ff ↔ δ σ (HasNot.not e) = some HasBool.tt)

def WellFormedSemanticEvalVal {P : PureExpr} [HasVal P]
    (δ : SemanticEval P) : Prop :=
    (∀ v v' σ, δ σ v = some v' → HasVal.value v') ∧
    (∀ v' σ, HasVal.value v' → δ σ v' = some v')

def WellFormedSemanticEvalVar {P : PureExpr} [HasFvar P] (δ : SemanticEval P)
    : Prop := ∀ e v σ, HasFvar.getFvar e = some v → δ σ e = σ v

-- EvalCmd
inductive EvalCmd {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] :
    SemanticEval P → SemanticStore P → Cmd P → SemanticStore P → Bool → Prop where
  | eval_assert_pass :
    δ σ e = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalCmd δ σ (.assert _ e _) σ false
  | eval_assert_fail :
    δ σ e = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalCmd δ σ (.assert _ e _) σ true
  | eval_assume :
    δ σ e = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalCmd δ σ (.assume _ e _) σ false
  | eval_cover :
    WellFormedSemanticEvalBool δ →
    EvalCmd δ σ (.cover _ e _) σ false
  | eval_init :
    EvalCmd δ σ (.init x ty e md) σ' false
  | eval_init_unconstrained :
    EvalCmd δ σ (.init x ty .nondet md) σ' false
  | eval_set :
    EvalCmd δ σ (.set x (.det e) md) σ' false
  | eval_set_nondet :
    EvalCmd δ σ (.set x .nondet md) σ' false

-- ============================================================
-- Env and ExtendEval
-- ============================================================

structure Env (P : PureExpr) where
  store : SemanticStore P
  eval  : SemanticEval P
  hasFailure : Bool := false

abbrev ExtendEval (P : PureExpr) := SemanticEval P → SemanticStore P → PureFunc P → SemanticEval P

-- ============================================================
-- Config and StepStmt
-- ============================================================

inductive Config (P : PureExpr) (CmdT : Type) : Type where
  | stmt : Stmt P CmdT → Env P → Config P CmdT
  | stmts : List (Stmt P CmdT) → Env P → Config P CmdT
  | terminal : Env P → Config P CmdT
  | exiting : Option String → Env P → Config P CmdT
  | block : Option String → Config P CmdT → Config P CmdT
  | seq : Config P CmdT → List (Stmt P CmdT) → Config P CmdT

def Config.getEnv : Config P CmdT → Env P
  | .stmt _ ρ => ρ
  | .stmts _ ρ => ρ
  | .terminal ρ => ρ
  | .exiting _ ρ => ρ
  | .block _ inner => inner.getEnv
  | .seq inner _ => inner.getEnv

def Config.getStore {P : PureExpr} {CmdT : Type} (cfg : Config P CmdT) : SemanticStore P :=
  cfg.getEnv.store

def Config.getEval {P : PureExpr} {CmdT : Type} (cfg : Config P CmdT) : SemanticEval P :=
  cfg.getEnv.eval

-- StepStmt (single step relation)
inductive StepStmt
    {CmdT : Type} (P : PureExpr) [HasBool P] [HasNot P]
    (EvalCmdR : EvalCmdParam P CmdT)
    (extendEval : ExtendEval P) :
    Config P CmdT → Config P CmdT → Prop where
  | step_cmd :
    EvalCmdR ρ.eval ρ.store c σ' hasAssertFailure →
    StepStmt P EvalCmdR extendEval
      (.stmt (.cmd c) ρ)
      (.terminal { ρ with store := σ', hasFailure := ρ.hasFailure || hasAssertFailure })
  | step_block :
    StepStmt P EvalCmdR extendEval
      (.stmt (.block label ss _) ρ)
      (.block (.some label) (.stmts ss ρ))
  | step_ite_true :
    ρ.eval ρ.store c = .some HasBool.tt →
    WellFormedSemanticEvalBool ρ.eval →
    StepStmt P EvalCmdR extendEval
      (.stmt (.ite (.det c) tss ess _) ρ) (.stmts tss ρ)
  | step_ite_false :
    ρ.eval ρ.store c = .some HasBool.ff →
    WellFormedSemanticEvalBool ρ.eval →
    StepStmt P EvalCmdR extendEval
      (.stmt (.ite (.det c) tss ess _) ρ) (.stmts ess ρ)
  | step_ite_nondet_true :
    StepStmt P EvalCmdR extendEval
      (.stmt (.ite .nondet tss ess _) ρ) (.stmts tss ρ)
  | step_ite_nondet_false :
    StepStmt P EvalCmdR extendEval
      (.stmt (.ite .nondet tss ess _) ρ) (.stmts ess ρ)
  | step_loop_enter {hasInvFailure : Bool} :
    ρ.eval ρ.store g = .some HasBool.tt →
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    WellFormedSemanticEvalBool ρ.eval →
    StepStmt P EvalCmdR extendEval
      (.stmt (.loop (.det g) m inv body md) ρ)
      (.block .none (.stmts (body ++ [.loop (.det g) m inv body md])
        { ρ with hasFailure := ρ.hasFailure || hasInvFailure }))
  | step_loop_exit {hasInvFailure : Bool} :
    ρ.eval ρ.store g = .some HasBool.ff →
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    WellFormedSemanticEvalBool ρ.eval →
    StepStmt P EvalCmdR extendEval
      (.stmt (.loop (.det g) m inv body _) ρ)
      (.terminal { ρ with hasFailure := ρ.hasFailure || hasInvFailure })
  | step_loop_nondet_enter {hasInvFailure : Bool} :
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    StepStmt P EvalCmdR extendEval
      (.stmt (.loop .nondet m inv body md) ρ)
      (.block .none (.stmts (body ++ [.loop .nondet m inv body md])
        { ρ with hasFailure := ρ.hasFailure || hasInvFailure }))
  | step_loop_nondet_exit {hasInvFailure : Bool} :
    (∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                 ρ.eval ρ.store le.2 = .some HasBool.ff) →
    (hasInvFailure ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) →
    StepStmt P EvalCmdR extendEval
      (.stmt (.loop .nondet m inv body _) ρ)
      (.terminal { ρ with hasFailure := ρ.hasFailure || hasInvFailure })
  | step_exit :
    StepStmt P EvalCmdR extendEval
      (.stmt (.exit label _) ρ) (.exiting label ρ)
  | step_funcDecl [HasSubstFvar P] [HasVarsPure P P.Expr] :
    StepStmt P EvalCmdR extendEval
      (.stmt (.funcDecl decl md) ρ)
      (.terminal { ρ with eval := extendEval ρ.eval ρ.store decl })
  | step_typeDecl :
    StepStmt P EvalCmdR extendEval
      (.stmt (.typeDecl _tc _md) ρ) (.terminal ρ)
  | step_stmts_nil :
    StepStmt P EvalCmdR extendEval
      (.stmts [] ρ) (.terminal ρ)
  | step_stmts_cons :
    StepStmt P EvalCmdR extendEval
      (.stmts (s :: ss) ρ) (.seq (.stmt s ρ) ss)
  | step_seq_inner :
    StepStmt P EvalCmdR extendEval inner inner' →
    StepStmt P EvalCmdR extendEval (.seq inner ss) (.seq inner' ss)
  | step_seq_done :
    StepStmt P EvalCmdR extendEval
      (.seq (.terminal ρ') ss) (.stmts ss ρ')
  | step_seq_exit :
    StepStmt P EvalCmdR extendEval
      (.seq (.exiting label ρ') ss) (.exiting label ρ')
  | step_block_body :
    StepStmt P EvalCmdR extendEval inner inner' →
    StepStmt P EvalCmdR extendEval (.block label inner) (.block label inner')
  | step_block_done :
    StepStmt P EvalCmdR extendEval
      (.block label (.terminal ρ')) (.terminal ρ')
  | step_block_exit_none :
    StepStmt P EvalCmdR extendEval
      (.block label (.exiting .none ρ')) (.terminal ρ')
  | step_block_exit_match :
    label = .some l →
    StepStmt P EvalCmdR extendEval
      (.block label (.exiting (.some l) ρ')) (.terminal ρ')
  | step_block_exit_mismatch :
    label ≠ .some l →
    StepStmt P EvalCmdR extendEval
      (.block label (.exiting (.some l) ρ')) (.exiting (.some l) ρ')

-- Multi-step
abbrev StepStmtStar (P : PureExpr) [HasBool P] [HasNot P]
    (EvalCmdR : EvalCmdParam P CmdT) (extendEval : ExtendEval P) :
    Config P CmdT → Config P CmdT → Prop :=
  ReflTrans (StepStmt P EvalCmdR extendEval)

-- ============================================================
-- Inversion lemmas (axiomatized)
-- ============================================================

axiom stmts_append_terminates {P : PureExpr} {CmdT : Type} [HasBool P] [HasNot P]
    (EvalCmdR : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    (ss₁ ss₂ : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmdR extendEval (.stmts (ss₁ ++ ss₂) ρ) (.terminal ρ')) :
    ∃ ρ₁, StepStmtStar P EvalCmdR extendEval (.stmts ss₁ ρ) (.terminal ρ₁) ∧
           StepStmtStar P EvalCmdR extendEval (.stmts ss₂ ρ₁) (.terminal ρ')

axiom seq_reaches_terminal {P : PureExpr} {CmdT : Type} [HasBool P] [HasNot P]
    (EvalCmdR : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmdR extendEval (.seq inner ss) (.terminal ρ')) :
    ∃ ρ₁, StepStmtStar P EvalCmdR extendEval inner (.terminal ρ₁) ∧
      StepStmtStar P EvalCmdR extendEval (.stmts ss ρ₁) (.terminal ρ')

axiom block_reaches_terminal {P : PureExpr} {CmdT : Type} [HasBool P] [HasNot P]
    (EvalCmdR : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    {inner : Config P CmdT} {l : Option String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmdR extendEval (.block l inner) (.terminal ρ')) :
    StepStmtStar P EvalCmdR extendEval inner (.terminal ρ') ∨
    (∃ lbl, StepStmtStar P EvalCmdR extendEval inner (.exiting lbl ρ'))

-- ============================================================
-- BasicBlock / CFG types
-- ============================================================

inductive DetTransferCmd (Label : Type) (P : PureExpr) where
  | condGoto (p : P.Expr) (lt lf : Label) (md : MetaData P := .empty)
  | finish (md : MetaData P := .empty)

def DetTransferCmd.goto {P : PureExpr} [HasBool P] {Label : Type} (l : Label) (md : MetaData P := .empty) : DetTransferCmd Label P :=
  condGoto HasBool.tt l l md

structure BasicBlock (TransferCmd CmdT : Type) where
  cmds : List CmdT
  transfer : TransferCmd

def DetBlock (Label CmdT : Type) (P : PureExpr) :=
  BasicBlock (DetTransferCmd Label P) CmdT

structure CFG (Label Block : Type) where
  entry : Label
  blocks : List (Label × Block)

-- ============================================================
-- CFGSemantics
-- ============================================================

inductive EvalCmds
    {CmdT : Type}
    (P : PureExpr)
    (EvalCmdR : EvalCmdParam P CmdT) :
    SemanticEval P → SemanticStore P → List CmdT → SemanticStore P → Bool → Prop where
  | eval_cmds_none :
    EvalCmds P EvalCmdR δ σ [] σ false
  | eval_cmds_some :
    EvalCmdR δ σ c σ' failed →
    EvalCmds P EvalCmdR δ σ' cs σ'' failed' →
    EvalCmds P EvalCmdR δ σ (c :: cs) σ'' (failed || failed')

inductive CFGConfig (l : Type) (P : PureExpr) : Type where
  | cont : l → SemanticStore P → Bool → CFGConfig l P
  | terminal : SemanticStore P → Bool → CFGConfig l P

inductive EvalDetBlock
    {CmdT : Type}
    (P : PureExpr)
    (EvalCmdR : EvalCmdParam P CmdT)
    (extendEval : ExtendEval P)
    [HasNot P] :
    SemanticStore P → DetBlock l CmdT P → CFGConfig l P → Prop where
  | step_goto_true :
    EvalCmds P EvalCmdR δ σ cs σ' failed →
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalDetBlock P EvalCmdR extendEval
      σ ⟨ cs, .condGoto c t e _ ⟩ (.cont t σ' failed)
  | step_goto_false :
    EvalCmds P EvalCmdR δ σ cs σ' failed →
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalDetBlock P EvalCmdR extendEval
      σ ⟨ cs, .condGoto c t e _ ⟩ (.cont e σ' failed)
  | step_terminal :
    EvalCmds P EvalCmdR δ σ cs σ' failed →
    EvalDetBlock P EvalCmdR extendEval
      σ ⟨ cs, .finish _ ⟩ (.terminal σ' failed)

def updateFailure : CFGConfig l P → Bool → CFGConfig l P
  | .cont t σ failed, failed' => .cont t σ (failed || failed')
  | .terminal σ failed, failed' => .terminal σ (failed || failed')

inductive StepCFG
    {Blk l CmdT : Type}
    [BEq l]
    (P : PureExpr)
    (EvalBlock : SemanticStore P → Blk → CFGConfig l P → Prop) :
    CFG l Blk → CFGConfig l P → CFGConfig l P → Prop where
  | eval_next :
    List.lookup t cfg.blocks = .some b →
    EvalBlock σ b config →
    StepCFG P EvalBlock cfg (.cont t σ failed) (updateFailure config failed)

def StepCFGStar
    {Blk l CmdT : Type}
    [BEq l]
    (P : PureExpr)
    (EvalBlock : SemanticStore P → Blk → CFGConfig l P → Prop)
    (cfg : CFG l Blk) :
    CFGConfig l P → CFGConfig l P → Prop :=
  ReflTrans (@StepCFG Blk l CmdT _ P EvalBlock cfg)

-- ============================================================
-- AssertId, isAtAssert
-- ============================================================

structure AssertId (P : PureExpr) where
  label : String
  expr  : P.Expr

def isAtAssert {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P) :
    Config P (Cmd P) → AssertId P → Prop
  | .stmt (.cmd (.assert label expr _)) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmts ((.cmd (.assert label expr _)) :: _) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmt (.loop _ _ inv _ _) _, aid => (aid.label, aid.expr) ∈ inv
  | .stmts ((.loop _ _ inv _ _) :: _) _, aid => (aid.label, aid.expr) ∈ inv
  | .block _ inner, aid => isAtAssert extendEval inner aid
  | .seq inner _, aid => isAtAssert extendEval inner aid
  | _, _ => False

-- ============================================================
-- DetBlocks, flushCmds, stmtsToBlocks, stmtsToCFG
-- ============================================================

abbrev DetBlocks (Label CmdT : Type) (P : PureExpr) := List (Label × DetBlock Label CmdT P)

def flushCmds {P : PureExpr} {CmdT : Type} [HasBool P]
    (pfx : String)
    (accum : List CmdT)
    (tr? : Option (DetTransferCmd String P))
    (k : String) :
    StringGenM (String × DetBlocks String CmdT P) := do
  if accum.isEmpty then
    pure (k, [])
  else
    let l ← StringGenState.gen pfx
    let b := (l, { cmds := accum.reverse, transfer := tr?.getD (.goto k) })
    pure (l, [b])

def stmtsToBlocks {P : PureExpr} {CmdT : Type}
    [HasBool P] [HasPassiveCmds P CmdT] [HasInit P CmdT]
    [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (k : String)
    (ss : List (Stmt P CmdT))
    (exitConts : List (Option String × String))
    (accum : List CmdT) :
    StringGenM (String × DetBlocks String CmdT P) :=
  match ss with
  | [] =>
    flushCmds "l$" accum .none k
  | .cmd c :: rest =>
    stmtsToBlocks k rest exitConts (c :: accum)
  | .funcDecl _ _ :: rest =>
    stmtsToBlocks k rest exitConts accum
  | .typeDecl _ _ :: rest =>
    stmtsToBlocks k rest exitConts accum
  | .block l bss md :: rest => do
    let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
    let (bl, bbs) ← stmtsToBlocks kNext bss ((.some l, kNext) :: exitConts) []
    let (accumEntry, accumBlocks) ← flushCmds "blk$" accum .none bl
    if l == bl then
      pure (accumEntry, accumBlocks ++ bbs ++ bsNext)
    else
      let b := (l, { cmds := [], transfer := .goto bl md })
      pure (l, accumBlocks ++ [b] ++ bbs ++ bsNext)
  | .ite c tss fss md :: rest => do
    let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
    let l ← StringGenState.gen "ite"
    let (tl, tbs) ← stmtsToBlocks kNext tss exitConts []
    let (fl, fbs) ← stmtsToBlocks kNext fss exitConts []
    let (condExpr, extraCmds) ← match c with
      | .det e => pure (e, [])
      | .nondet => do
        let freshName ← StringGenState.gen "$__nondet_ite$"
        let ident := HasIdent.ident (P := P) freshName
        let initCmd := HasInit.init ident HasBool.boolTy .nondet MetaData.empty
        pure (HasFvar.mkFvar ident, [initCmd])
    let (accumEntry, accumBlocks) ← flushCmds "ite$" (accum ++ extraCmds)
      (.some (.condGoto condExpr tl fl md)) l
    pure (accumEntry, accumBlocks ++ tbs ++ fbs ++ bsNext)
  | .loop c m is bss md :: rest => do
    let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
    let lentry ← StringGenState.gen "loop_entry$"
    let (measureCmds, bodyK, decreaseBlocks) ←
      match m with
      | none => pure ([], lentry, [])
      | some mExpr => do
        let mLabel ← StringGenState.gen "loop_measure$"
        let mIdent := HasIdent.ident mLabel
        let mOldExpr := HasFvar.mkFvar mIdent
        let initCmd  := HasInit.init mIdent HasIntOrder.intTy .nondet MetaData.empty
        let assumeCmd := HasPassiveCmds.assume s!"assume_{mLabel}"
                           (HasIntOrder.eq mOldExpr mExpr) MetaData.empty
        let lbCmd    := HasPassiveCmds.assert s!"measure_lb_{mLabel}"
                           (HasNot.not (HasIntOrder.lt mOldExpr HasIntOrder.zero)) MetaData.empty
        let decCmd   := HasPassiveCmds.assert s!"measure_decrease_{mLabel}"
                           (HasIntOrder.lt mExpr mOldExpr) MetaData.empty
        let ldec ← StringGenState.gen "measure_decrease$"
        let decBlock := (ldec, { cmds := [decCmd], transfer := .goto lentry })
        pure ([initCmd, assumeCmd, lbCmd], ldec, [decBlock])
    let (bl, bbs) ← stmtsToBlocks bodyK bss ((.none, kNext) :: exitConts) []
    let invCmds : List CmdT ←
      is.mapM (fun (srcLabel, i) => do
        let assertLabel ←
          if srcLabel.isEmpty then StringGenState.gen "inv$"
          else pure srcLabel
        pure (HasPassiveCmds.assert assertLabel i MetaData.empty))
    match c with
    | .det e =>
      let b := (lentry, { cmds := invCmds ++ measureCmds, transfer := .condGoto e bl kNext md })
      let (accumEntry, accumBlocks) ← flushCmds "before_loop$" accum .none lentry
      pure (accumEntry, accumBlocks ++ [b] ++ bbs ++ decreaseBlocks ++ bsNext)
    | .nondet => do
      let freshName ← StringGenState.gen "$__nondet_loop$"
      let ident := HasIdent.ident (P := P) freshName
      let initCmd := HasInit.init ident HasBool.boolTy .nondet MetaData.empty
      let b := (lentry, { cmds := [initCmd] ++ invCmds ++ measureCmds,
                          transfer := .condGoto (HasFvar.mkFvar ident) bl kNext md })
      let (accumEntry, accumBlocks) ← flushCmds "before_loop$" accum .none lentry
      pure (accumEntry, accumBlocks ++ [b] ++ bbs ++ decreaseBlocks ++ bsNext)
  | .exit l? md :: _ => do
    let bk :=
      match (l?, exitConts) with
      | (.none, []) => k
      | (.none, (_, k) :: _) => k
      | (.some l, _) =>
        match exitConts.lookup (.some l) with
        | .some k => k
        | .none => k
    let exitName :=
      match l? with
      | .some l => s!"block${l}$"
      | .none => "block$"
    flushCmds exitName accum (.some (.goto bk md)) bk

def stmtsToCFGM {P : PureExpr} {CmdT : Type}
    [HasBool P] [HasPassiveCmds P CmdT] [HasInit P CmdT]
    [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (ss : List (Stmt P CmdT)) :
    StringGenM (CFG String (DetBlock String CmdT P)) := do
  let lend ← StringGenState.gen "end$"
  let bend := (lend, { cmds := [], transfer := .finish })
  let (l, bs) ← stmtsToBlocks lend ss [] []
  pure { entry := l, blocks := bs ++ [bend] }

def stmtsToCFG {P : PureExpr} {CmdT : Type}
    [HasBool P] [HasPassiveCmds P CmdT] [HasInit P CmdT]
    [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (ss : List (Stmt P CmdT)) :
    CFG String (DetBlock String CmdT P) :=
  (stmtsToCFGM ss StringGenState.emp).fst

-- ============================================================
-- Specification.Lang
-- ============================================================

namespace Specification

structure Lang (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P] where
  StmtT : Type
  CfgT  : Type
  star  : CfgT → CfgT → Prop
  stmtCfg     : StmtT → Env P → CfgT
  terminalCfg : Env P → CfgT
  exitingCfg  : Option String → Env P → CfgT
  isAtAssert  : CfgT → AssertId P → Prop
  getEnv      : CfgT → Env P

abbrev Lang.imperative (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P]
    (CmdT : Type) (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
    (isAtAssertFn : Config P CmdT → AssertId P → Prop) : Lang P :=
  ⟨Stmt P CmdT, Config P CmdT, StepStmtStar P evalCmd extendEval,
   .stmt, .terminal, .exiting, isAtAssertFn, Config.getEnv⟩

def AssertValid {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (L : Lang P) (s : L.StmtT) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : L.CfgT),
    L.star (L.stmtCfg s ρ₀) cfg →
    L.isAtAssert cfg a →
    (L.getEnv cfg).eval (L.getEnv cfg).store a.expr = some HasBool.tt

end Specification

-- ============================================================
-- StructuredToUnstructuredCorrect
-- ============================================================

namespace StructuredToUnstructuredCorrect

open Specification

/-! ## Lang instances -/

abbrev Lang.structured {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P]
    [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (@EvalCmd P _ _ _) extendEval (isAtAssert extendEval)

structure CFGLangConfig (P : PureExpr) where
  cfgConfig : CFGConfig String P
  eval : SemanticEval P

def CFGLangConfig.toEnv {P : PureExpr} (c : CFGLangConfig P) : Env P :=
  match c.cfgConfig with
  | .cont _ σ f => ⟨σ, c.eval, f⟩
  | .terminal σ f => ⟨σ, c.eval, f⟩

def cfgIsAtAssert {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (cfg : CFG String (DetBlock String (Cmd P) P))
    : CFGLangConfig P → AssertId P → Prop
  | ⟨.cont lbl _ _, _⟩, aid =>
    match cfg.blocks.lookup lbl with
    | some blk => match blk.cmds with
      | .assert label expr _ :: _ => aid.label = label ∧ aid.expr = expr
      | _ => False
    | none => False
  | ⟨.terminal _ _, _⟩, _ => False

abbrev Lang.cfg {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P]
    [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (cfg : CFG String (DetBlock String (Cmd P) P)) : Lang P where
  StmtT := CFG String (DetBlock String (Cmd P) P)
  CfgT := CFGLangConfig P
  star := fun c₁ c₂ =>
    @StepCFGStar _ _ (Cmd P) _ P (EvalDetBlock P (@EvalCmd P _ _ _) extendEval) cfg c₁.cfgConfig c₂.cfgConfig
  stmtCfg := fun _ ρ => ⟨.cont cfg.entry ρ.store false, ρ.eval⟩
  terminalCfg := fun ρ => ⟨.terminal ρ.store ρ.hasFailure, ρ.eval⟩
  exitingCfg := fun _ ρ => ⟨.terminal ρ.store ρ.hasFailure, ρ.eval⟩
  isAtAssert := cfgIsAtAssert cfg
  getEnv := CFGLangConfig.toEnv

/-! ## Abbreviations -/

abbrev StepDetCFGStar {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cfg : CFG String (DetBlock String (Cmd P) P)) :=
  @StepCFGStar _ _ (Cmd P) _ P (EvalDetBlock P (@EvalCmd P _ _ _) extendEval) cfg

/-! ## Helper: flushCmds simulation -/

private theorem evalCmds_of_stmtStar_cmds_gen {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cmds : List (Cmd P)) (δ : SemanticEval P) (σ σ' : SemanticStore P)
    (failed : Bool) (hf : Bool)
    (h : EvalCmds P (@EvalCmd P _ _ _) δ σ cmds σ' failed) :
    StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (cmds.map Stmt.cmd) ⟨σ, δ, hf⟩)
      (.terminal ⟨σ', δ, hf || failed⟩) := by
  induction h generalizing hf with
  | eval_cmds_none =>
    simp [List.map, Bool.or_false]
    exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
  | eval_cmds_some hcmd hcmds ih =>
    simp only [List.map]
    apply ReflTrans.step _ _ _ StepStmt.step_stmts_cons
    apply ReflTrans.step _ _ _ (StepStmt.step_seq_inner (StepStmt.step_cmd hcmd))
    apply ReflTrans.step _ _ _ StepStmt.step_seq_done
    rw [← Bool.or_assoc]
    exact ih (hf || _)

private theorem evalCmds_of_stmtStar_cmds {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cmds : List (Cmd P)) (δ : SemanticEval P) (σ σ' : SemanticStore P)
    (failed : Bool)
    (h : EvalCmds P (@EvalCmd P _ _ _) δ σ cmds σ' failed) :
    StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (cmds.map Stmt.cmd) ⟨σ, δ, false⟩)
      (.terminal ⟨σ', δ, failed⟩) := by
  have := evalCmds_of_stmtStar_cmds_gen extendEval cmds δ σ σ' failed false h
  simp [Bool.false_or] at this
  exact this

private theorem stmtStar_cmds_to_evalCmds_gen {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cmds : List (Cmd P)) (ρ₀ ρ' : Env P)
    (h : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (cmds.map Stmt.cmd) ρ₀) (.terminal ρ')) :
    ∃ failed, EvalCmds P (@EvalCmd P _ _ _) ρ₀.eval ρ₀.store cmds ρ'.store failed ∧
      ρ'.hasFailure = (ρ₀.hasFailure || failed) := by
  induction cmds generalizing ρ₀ with
  | nil =>
    simp [List.map] at h
    have hnil : ρ' = ρ₀ := by
      cases h with
      | step _ _ _ hstep hrest => cases hstep with
        | step_stmts_nil => cases hrest with
          | refl => rfl
          | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    subst hnil
    exact ⟨false, EvalCmds.eval_cmds_none, by simp⟩
  | cons c cs ih =>
    simp [List.map] at h
    have ⟨ρ₁, hcmd_star, hrest⟩ := stmts_append_terminates (@EvalCmd P _ _ _) extendEval
      [.cmd c] (List.map Stmt.cmd cs) ρ₀ ρ' h
    cases hcmd_star with
    | step _ _ _ hstep1 hrest1 => cases hstep1 with
      | step_stmts_cons =>
        have ⟨ρ_s, h_s_term, h_nil⟩ := seq_reaches_terminal (@EvalCmd P _ _ _) extendEval hrest1
        have hrest' : StepStmtStar P (@EvalCmd P _ _ _) extendEval
            (.stmts (List.map Stmt.cmd cs) ρ_s) (.terminal ρ') := by
          cases h_nil with
          | step _ _ _ hstep3 hrest3 => cases hstep3 with
            | step_stmts_nil => cases hrest3 with
              | refl => exact hrest
              | step _ _ _ h _ => exact absurd h (by intro h; cases h)
        cases h_s_term with
        | step _ _ _ hstep2 hrest2 => cases hstep2 with
          | step_cmd heval =>
            cases hrest2 with
            | refl =>
              have ⟨failed', heval_rest, hfail'⟩ := ih _ hrest'
              refine ⟨_ || failed', EvalCmds.eval_cmds_some heval heval_rest, ?_⟩
              rw [hfail', Bool.or_assoc]
            | step _ _ _ h _ => exact absurd h (by intro h; cases h)

/-! ## Generalized simulation -/

theorem stmtsToBlocks_simulation {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (allBlocks : DetBlocks String (Cmd P) P)
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (stmtsToBlocks k ss exitConts accum gen) = ((entry, blocks), gen'))
    (σ_base : SemanticStore P)
    (hf_base : Bool)
    (hf_accum : Bool)
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (h_term : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts ss ρ₀) (.terminal ρ'))
    (h_accum : EvalCmds P (@EvalCmd P _ _ _) ρ₀.eval σ_base accum.reverse ρ₀.store hf_accum)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks) :
    StepDetCFGStar extendEval cfg
      (.cont entry σ_base hf_base)
      (.cont k ρ'.store ρ'.hasFailure) := by
  sorry

theorem stmtsToBlocks_simulation_exiting {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (allBlocks : DetBlocks String (Cmd P) P)
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (stmtsToBlocks k ss exitConts accum gen) = ((entry, blocks), gen'))
    (σ_base : SemanticStore P)
    (hf_base : Bool)
    (hf_accum : Bool)
    (ρ₀ ρ' : Env P) (lbl : Option String)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (h_exit : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts ss ρ₀) (.exiting lbl ρ'))
    (h_accum : EvalCmds P (@EvalCmd P _ _ _) ρ₀.eval σ_base accum.reverse ρ₀.store hf_accum)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks) :
    ∃ σ_final failed, StepDetCFGStar extendEval cfg
      (.cont entry σ_base hf_base)
      (.terminal σ_final failed) ∧ σ_final = ρ'.store := by
  sorry

/-! ## Per-constructor simulation lemmas -/

private theorem cmd_simulation {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (c : Cmd P) (rest : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (h_term : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (Stmt.cmd c :: rest) ρ₀) (.terminal ρ')) :
    ∃ ρ_mid,
      StepStmtStar P (@EvalCmd P _ _ _) extendEval
        (.stmts rest ρ_mid) (.terminal ρ') := by
  have ⟨ρ₁, _, htail⟩ := stmts_append_terminates (@EvalCmd P _ _ _) extendEval
    [.cmd c] rest ρ₀ ρ' (by simpa using h_term)
  exact ⟨ρ₁, htail⟩

theorem block_simulation {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (l : String) (body rest : List (Stmt P (Cmd P)))
    (md : MetaData P)
    (ρ₀ ρ' : Env P)
    (h_term : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (Stmt.block l body md :: rest) ρ₀) (.terminal ρ')) :
    ∃ ρ_mid,
      (StepStmtStar P (@EvalCmd P _ _ _) extendEval
        (.stmts body ρ₀) (.terminal ρ_mid) ∨
       ∃ lbl, StepStmtStar P (@EvalCmd P _ _ _) extendEval
        (.stmts body ρ₀) (.exiting lbl ρ_mid)) ∧
      StepStmtStar P (@EvalCmd P _ _ _) extendEval
        (.stmts rest ρ_mid) (.terminal ρ') := by
  have ⟨ρ₁, hblock_star, htail⟩ := stmts_append_terminates (@EvalCmd P _ _ _) extendEval
    [.block l body md] rest ρ₀ ρ' (by simpa using h_term)
  have := hblock_star
  cases this
  rename_i y hy₁ hy₂
  cases hy₁
  obtain ⟨ρ_inner, h_inner⟩ := seq_reaches_terminal _ _ hy₂
  cases h_inner.2
  cases ‹StepStmt P EvalCmd extendEval (Config.stmts [] ρ_inner) _›
  cases ‹ReflTrans (StepStmt P EvalCmd extendEval) (Config.terminal ρ_inner) (Config.terminal ρ₁)›
  · cases h_inner.1
    cases ‹StepStmt P EvalCmd extendEval (Config.stmt (Stmt.block l body md) ρ₀) _›
    have := block_reaches_terminal _ _ ‹_›
    exact ⟨ρ₁, this, htail⟩
  · cases ‹StepStmt P EvalCmd extendEval (Config.terminal ρ_inner) _›

theorem ite_simulation {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (c : ExprOrNondet P) (tss fss rest : List (Stmt P (Cmd P)))
    (md : MetaData P)
    (ρ₀ ρ' : Env P)
    (h_term : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (Stmt.ite c tss fss md :: rest) ρ₀) (.terminal ρ')) :
    ∃ ρ_mid,
      (StepStmtStar P (@EvalCmd P _ _ _) extendEval (.stmts tss ρ₀) (.terminal ρ_mid) ∨
       StepStmtStar P (@EvalCmd P _ _ _) extendEval (.stmts fss ρ₀) (.terminal ρ_mid)) ∧
      StepStmtStar P (@EvalCmd P _ _ _) extendEval
        (.stmts rest ρ_mid) (.terminal ρ') := by
  have ⟨ρ₁, hite_star, htail⟩ := stmts_append_terminates (@EvalCmd P _ _ _) extendEval
    [.ite c tss fss md] rest ρ₀ ρ' (by simpa using h_term)
  rcases hite_star with ⟨ρ₁, hite_star⟩
  cases ‹StepStmt _ _ _ _ _›
  rename_i h
  obtain ⟨ρ₂, h₁, h₂⟩ := seq_reaches_terminal _ _ h
  cases h₁
  cases ‹StepStmt _ _ _ _ _›
  · cases h₂
    cases ‹StepStmt _ _ _ _ _›
    cases ‹ReflTrans (StepStmt P EvalCmd extendEval) (Config.terminal ρ₂) (Config.terminal ρ₁)›
    · exact ⟨ρ₁, Or.inl ‹_›, htail⟩
    · cases ‹StepStmt _ _ _ _ _›
  · cases h₂
    cases ‹StepStmt _ _ _ _ _›
    rename_i h₁ h₂ h₃ h₄
    cases h₄
    · exact ⟨ρ₁, Or.inr h₃, htail⟩
    · cases ‹StepStmt _ _ _ _ _›
  · cases h₂
    cases ‹StepStmt _ _ _ _ _›
    cases ‹ReflTrans (StepStmt P EvalCmd extendEval) (Config.terminal ρ₂) (Config.terminal ρ₁)›
    · exact ⟨ρ₁, Or.inl ‹_›, htail⟩
    · cases ‹StepStmt _ _ _ _ _›
  · cases h₂
    cases ‹StepStmt _ _ _ _ _›
    rename_i h₁ h₂
    cases h₂
    · exact ⟨ρ₁, Or.inr h₁, htail⟩
    · cases ‹StepStmt _ _ _ _ _›

private theorem loop_simulation {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (c : ExprOrNondet P) (m : Option P.Expr)
    (inv : List (String × P.Expr)) (body rest : List (Stmt P (Cmd P)))
    (md : MetaData P)
    (ρ₀ ρ' : Env P)
    (h_term : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (Stmt.loop c m inv body md :: rest) ρ₀) (.terminal ρ')) :
    ∃ ρ_mid,
      StepStmtStar P (@EvalCmd P _ _ _) extendEval
        (.stmts rest ρ_mid) (.terminal ρ') := by
  have ⟨ρ₁, _, htail⟩ := stmts_append_terminates (@EvalCmd P _ _ _) extendEval
    [.loop c m inv body md] rest ρ₀ ρ' (by simpa using h_term)
  exact ⟨ρ₁, htail⟩

/-! ## Top-level theorems -/

/-- Specification lemma: `stmtsToCFG` produces a CFG whose blocks come from
`stmtsToBlocks` plus a terminal block, and whose entry matches. -/
theorem stmtsToCFG_stmtsToBlocks_spec {P : PureExpr} {CmdT : Type}
    [HasBool P] [HasPassiveCmds P CmdT] [HasInit P CmdT]
    [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (ss : List (Stmt P CmdT)) :
    ∃ (lend : String) (gen gen' : StringGenState)
      (entry : String) (blocks : DetBlocks String CmdT P),
      stmtsToBlocks lend ss [] [] gen = ((entry, blocks), gen') ∧
      (stmtsToCFG ss).entry = entry ∧
      (∀ b ∈ blocks, b ∈ (stmtsToCFG ss).blocks) ∧
      (stmtsToCFG ss).blocks.lookup lend =
        some ({ cmds := [], transfer := .finish } : BasicBlock (DetTransferCmd String P) CmdT) := by
  let lend : String := (StringGenState.gen "end$" StringGenState.emp).1
  let gen : StringGenState := (StringGenState.gen "end$" StringGenState.emp).2
  let r := stmtsToBlocks lend ss ([] : List (Option String × String)) ([] : List CmdT) gen
  let entry := r.1.1
  let blocks := r.1.2
  let gen' := r.2
  have h_stmtsToCFG : stmtsToCFG ss = { entry := entry, blocks := blocks ++ [(lend, { cmds := [], transfer := .finish })] } := by
    unfold stmtsToCFG stmtsToCFGM
    simp only [bind, StateT.bind, pure, StateT.pure, StringGenState.gen,
      Counter.genCounter, StringGenState.emp, Counter.CounterState.emp]
    rfl
  refine ⟨lend, gen, gen', entry, blocks, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [h_stmtsToCFG]
  · intro b hb
    simp [h_stmtsToCFG]
    exact Or.inl hb
  · simp [h_stmtsToCFG]
    /- NOTE: This requires showing that `lend` does not appear as a key in `blocks`.
       This holds for all generated labels (they have counter ≥ 1 while lend has counter 0),
       but user-provided block labels (from Stmt.block l ...) could theoretically equal lend.
       A fully correct proof would need a freshness assumption on user labels. -/
    sorry

private theorem end_block_terminal {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (lend : String) (σ : SemanticStore P) (δ : SemanticEval P) (failed : Bool)
    (h_lookup : cfg.blocks.lookup lend =
      some ({ cmds := [], transfer := .finish } : DetBlock String (Cmd P) P)) :
    StepDetCFGStar extendEval cfg
      (.cont lend σ failed)
      (.terminal σ failed) := by
  apply ReflTrans.step _ _ _ _ (ReflTrans.refl _)
  exact StepCFG.eval_next h_lookup
    (EvalDetBlock.step_terminal (EvalCmds.eval_cmds_none (P := P) (δ := δ)))

theorem stmtsToCFG_terminal {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_term : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts ss ρ₀) (.terminal ρ')) :
    let cfg := stmtsToCFG ss
    StepDetCFGStar extendEval cfg
      (.cont cfg.entry ρ₀.store false)
      (.terminal ρ'.store ρ'.hasFailure) := by
  intro cfg
  have ⟨lend, gen, gen', entry, blocks, h_gen, h_entry, h_blocks, h_lend⟩ :=
    stmtsToCFG_stmtsToBlocks_spec ss
  rw [h_entry]
  have h_accum : EvalCmds P (@EvalCmd P _ _ _) ρ₀.eval ρ₀.store [].reverse ρ₀.store false :=
    EvalCmds.eval_cmds_none
  have h_hf : ρ₀.hasFailure = (false || false) := by simp [hf₀]
  have h_sim := stmtsToBlocks_simulation extendEval lend ss [] [] blocks gen gen' entry blocks
      h_gen ρ₀.store false false ρ₀ ρ' hwfb hwfv h_term h_accum h_hf cfg h_blocks
  have h_end := end_block_terminal extendEval cfg lend ρ'.store ρ'.eval ρ'.hasFailure h_lend
  exact ReflTrans_Transitive _ _ _ _ h_sim h_end

theorem stmtsToCFG_exiting {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P) (lbl : Option String)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_exit : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts ss ρ₀) (.exiting lbl ρ')) :
    let cfg := stmtsToCFG ss
    ∃ σ_final failed,
      StepDetCFGStar extendEval cfg
        (.cont cfg.entry ρ₀.store false)
        (.terminal σ_final failed) ∧
      σ_final = ρ'.store := by
  intro cfg
  have ⟨lend, gen, gen', entry, blocks, h_gen, h_entry, h_blocks, _⟩ :=
    stmtsToCFG_stmtsToBlocks_spec ss
  rw [h_entry]
  have h_accum : EvalCmds P (@EvalCmd P _ _ _) ρ₀.eval ρ₀.store [].reverse ρ₀.store false :=
    EvalCmds.eval_cmds_none
  have h_hf : ρ₀.hasFailure = (false || false) := by simp [hf₀]
  exact stmtsToBlocks_simulation_exiting extendEval lend ss [] [] blocks gen gen' entry blocks
    h_gen ρ₀.store false false ρ₀ ρ' lbl hwfb hwfv h_exit h_accum h_hf cfg h_blocks

/-! ## Main theorems -/

theorem structuredToUnstructured_sound {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_term : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts ss ρ₀) (.terminal ρ')) :
    let cfg := stmtsToCFG ss
    StepDetCFGStar extendEval cfg
      (.cont cfg.entry ρ₀.store false)
      (.terminal ρ'.store ρ'.hasFailure) :=
  stmtsToCFG_terminal extendEval ss ρ₀ ρ' hwfb hwfv hf₀ h_term

theorem structuredToUnstructured_complete {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ : Env P) (σ_final : SemanticStore P) (failed : Bool)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_exits : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks [] ss)
    (h_cfg : let cfg := stmtsToCFG ss
             StepDetCFGStar extendEval cfg
               (.cont cfg.entry ρ₀.store false)
               (.terminal σ_final failed)) :
    ∃ ρ' : Env P,
      ρ'.store = σ_final ∧ ρ'.hasFailure = failed ∧
      StepStmtStar P (@EvalCmd P _ _ _) extendEval
        (.stmts ss ρ₀) (.terminal ρ') := by
  sorry

end StructuredToUnstructuredCorrect

end Imperative
