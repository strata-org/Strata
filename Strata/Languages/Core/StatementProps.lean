/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.DL.Imperative.StmtProps
import Strata.DL.Imperative.CmdProps
import Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExprWF
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd

/-! # Properties of Core statements

Per-constructor equations for `calledProcedureNames`, for call arguments, for `mapStmtTys` and
`mapStmtsTys` (defined through the well-founded `Stmt.mapExpr` and `Block.mapExpr`), the
identity laws `mapCmdTys_id` and `mapStmtsTys_id`, and equations for
`Statement.noCalls` and `Statements.noCalls`.

Key theorems: `Statements.calledProcedureNames_cons`, `Statement.calledProcedureNames_ite`,
`CallArg.getInputExprs_cons_*` and `CallArg.getLhs_cons_*`. -/

namespace Core

open Lambda Imperative

public section

/-- A standard command calls no procedure. -/
@[simp] theorem CmdExt.calledProcedureNames_cmd (c : Imperative.Cmd Expression) :
    CmdExt.calledProcedureNames (.cmd c) = [] := by
  simp only [CmdExt.calledProcedureNames, Command.callSites, List.map_nil]

/-- A call calls exactly its callee. -/
@[simp] theorem CmdExt.calledProcedureNames_call (pname : String)
    (tyArgs : Option (List Expression.Ty))
    (args : List (CallArg Expression)) (md : MetaData Expression) :
    CmdExt.calledProcedureNames (.call pname tyArgs args md) = [pname] := by
  simp only [CmdExt.calledProcedureNames, Command.callSites, List.map_cons, List.map_nil]

/-- A command statement calls exactly the procedures called by its command. -/
@[simp] theorem Statement.calledProcedureNames_cmd (c : Command) :
    Statement.calledProcedureNames (.cmd c) = CmdExt.calledProcedureNames c := by
  simp only [Statement.calledProcedureNames, CmdExt.calledProcedureNames, Statement.callSites]

/-- A block calls exactly the procedures called by its body. -/
@[simp] theorem Statement.calledProcedureNames_block (label : String) (b : Statements)
    (md : MetaData Expression) :
    Statement.calledProcedureNames (.block label b md) = Statements.calledProcedureNames b := by
  simp only [Statement.calledProcedureNames, Statements.calledProcedureNames, Statement.callSites]

/-- A conditional calls the procedures called by either branch. -/
@[simp] theorem Statement.calledProcedureNames_ite (cond : ExprOrNondet Expression)
    (thenb elseb : Statements) (md : MetaData Expression) :
    Statement.calledProcedureNames (.ite cond thenb elseb md)
      = Statements.calledProcedureNames thenb ++ Statements.calledProcedureNames elseb := by
  simp only [Statement.calledProcedureNames, Statements.calledProcedureNames, Statement.callSites,
    List.map_append]

/-- A loop calls exactly the procedures called by its body. -/
@[simp] theorem Statement.calledProcedureNames_loop (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr) (invariants : List (String × Expression.Expr))
    (b : Statements) (md : MetaData Expression) :
    Statement.calledProcedureNames (.loop guard measure invariants b md)
      = Statements.calledProcedureNames b := by
  simp only [Statement.calledProcedureNames, Statements.calledProcedureNames, Statement.callSites]

/-- An exit statement calls no procedure. -/
@[simp] theorem Statement.calledProcedureNames_exit (label : String) (md : MetaData Expression) :
    Statement.calledProcedureNames (.exit label md) = [] := by
  simp only [Statement.calledProcedureNames, Statement.callSites, List.map_nil]

/-- A local type declaration calls no procedure. -/
@[simp] theorem Statement.calledProcedureNames_typeDecl (tc : TypeConstructor)
    (md : MetaData Expression) :
    Statement.calledProcedureNames (.typeDecl tc md) = [] := by
  simp only [Statement.calledProcedureNames, Statement.callSites, List.map_nil]

/-- An empty statement list calls no procedure. -/
@[simp] theorem Statements.calledProcedureNames_nil :
    Statements.calledProcedureNames [] = [] := by
  simp only [Statements.calledProcedureNames, Statements.callSites, List.map_nil]

/-- A nonempty statement list calls the procedures called by its head and tail. -/
@[simp] theorem Statements.calledProcedureNames_cons (s : Statement) (ss : Statements) :
    Statements.calledProcedureNames (s :: ss)
      = Statement.calledProcedureNames s ++ Statements.calledProcedureNames ss := by
  simp only [Statements.calledProcedureNames, Statement.calledProcedureNames,
    Statements.callSites, List.map_append]

/-- Called procedure names distribute over statement-list append. -/
@[simp] theorem Statements.calledProcedureNames_append (as bs : List Statement) :
    Statements.calledProcedureNames (as ++ bs)
      = Statements.calledProcedureNames as ++ Statements.calledProcedureNames bs := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.cons_append, Statements.calledProcedureNames_cons, ih,
      List.append_assoc]

/-- An input argument contributes its expression to the call inputs. -/
theorem CallArg.getInputExprs_cons_inArg (e : Expression.Expr)
    (rest : List (CallArg Expression)) :
    CallArg.getInputExprs (.inArg e :: rest) = e :: CallArg.getInputExprs rest := by
  simp [CallArg.getInputExprs, Calls.getInputExprs]

/-- An in-out argument contributes an unannotated variable expression to the call inputs. -/
theorem CallArg.getInputExprs_cons_inoutArg (id : Expression.Ident)
    (rest : List (CallArg Expression)) :
    CallArg.getInputExprs (.inoutArg id :: rest)
      = LExpr.fvar Core.coreLoc id none :: CallArg.getInputExprs rest := by
  rfl

/-- An output argument contributes no expression to the call inputs. -/
theorem CallArg.getInputExprs_cons_outArg (id : Expression.Ident)
    (rest : List (CallArg Expression)) :
    CallArg.getInputExprs (.outArg id :: rest) = CallArg.getInputExprs rest := by
  simp [CallArg.getInputExprs, Calls.getInputExprs]

/-- An input argument contributes no assigned variable. -/
theorem CallArg.getLhs_cons_inArg (e : Expression.Expr)
    (rest : List (CallArg Expression)) :
    CallArg.getLhs (.inArg e :: rest) = CallArg.getLhs rest := by
  simp [CallArg.getLhs]

/-- An in-out argument contributes its identifier to the assigned variables. -/
theorem CallArg.getLhs_cons_inoutArg (id : Expression.Ident)
    (rest : List (CallArg Expression)) :
    CallArg.getLhs (.inoutArg id :: rest) = id :: CallArg.getLhs rest := by
  simp [CallArg.getLhs]

/-- An output argument contributes its identifier to the assigned variables. -/
theorem CallArg.getLhs_cons_outArg (id : Expression.Ident)
    (rest : List (CallArg Expression)) :
    CallArg.getLhs (.outArg id :: rest) = id :: CallArg.getLhs rest := by
  simp [CallArg.getLhs]

/-- Rewriting a command's type annotations with `f` rewrites the type arguments and the `inArg`
    expressions of the call it is, if any, and leaves the rest of the call alone. -/
theorem Command.callSites_mapCmdTys (f : LMonoTy → LMonoTy) (c : Command) :
    Command.callSites (mapCmdTys f c) =
      (Command.callSites c).map fun cs =>
        { cs with tyArgs := cs.tyArgs.map (·.map (mapLTyTys f)),
                  args := cs.args.map (CallArg.mapInput (mapExprTys f)) } := by
  cases c with
  | cmd cc => cases cc <;> rfl
  | call => rfl

/-- `replaceInArgs` keeps the assigned variables of a call. -/
theorem CallArg.getLhs_replaceInArgs (args : List (CallArg Expression))
    (es : List Expression.Expr) :
    CallArg.getLhs (CallArg.replaceInArgs args es) = CallArg.getLhs args := by
  simp only [CallArg.replaceInArgs]
  induction args generalizing es with
  | nil => rfl
  | cons a rest ih =>
    simp only [CallArg.getLhs] at ih ⊢
    match a, es with
    | .inArg _, e :: es => simp [CallArg.replaceInArgs.go, ih]
    | .inArg _, [] => simp [CallArg.replaceInArgs.go, ih]
    | .inoutArg _, e :: es => simp [CallArg.replaceInArgs.go, ih]
    | .inoutArg _, [] => simp [CallArg.replaceInArgs.go, ih]
    | .outArg _, es => simp [CallArg.replaceInArgs.go, ih]

/-- Each input after `replaceInArgs` is a replacement or an assigned variable of the call. -/
theorem CallArg.mem_getInputExprs_replaceInArgs :
    ∀ (args : List (CallArg Expression)) (es : List Expression.Expr),
      (CallArg.getInputExprs args).length ≤ es.length →
      ∀ e ∈ CallArg.getInputExprs (CallArg.replaceInArgs args es),
        e ∈ es ∨ ∃ id ∈ CallArg.getLhs args, e = LExpr.fvar Core.coreLoc id none := by
  intro args
  simp only [CallArg.replaceInArgs]
  induction args with
  | nil =>
    intro es _ e he
    simp only [CallArg.replaceInArgs.go, CallArg.getInputExprs, Calls.getInputExprs,
      List.filterMap_nil, List.not_mem_nil] at he
  | cons a rest ih =>
    intro es hlen e he
    match a, es with
    | .inArg e0, e1 :: es1 =>
      simp only [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_inArg,
        List.mem_cons] at he
      simp only [CallArg.getInputExprs_cons_inArg, List.length_cons] at hlen
      rcases he with rfl | he
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih es1 (by omega) e he with hmem | ⟨id, hid, heq⟩
        · exact Or.inl (List.mem_cons_of_mem _ hmem)
        · exact Or.inr ⟨id, by simpa [CallArg.getLhs_cons_inArg] using hid, heq⟩
    | .inArg e0, [] =>
      simp only [CallArg.getInputExprs_cons_inArg, List.length_cons, List.length_nil] at hlen
      omega
    | .inoutArg id0, e1 :: es1 =>
      simp only [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_inoutArg,
        List.mem_cons] at he
      simp only [CallArg.getInputExprs_cons_inoutArg, List.length_cons] at hlen
      rcases he with rfl | he
      · exact Or.inr ⟨id0, by simp [CallArg.getLhs_cons_inoutArg], rfl⟩
      · rcases ih es1 (by omega) e he with hmem | ⟨id, hid, heq⟩
        · exact Or.inl (List.mem_cons_of_mem _ hmem)
        · exact Or.inr ⟨id, by simp [CallArg.getLhs_cons_inoutArg, hid], heq⟩
    | .inoutArg id0, [] =>
      simp only [CallArg.getInputExprs_cons_inoutArg, List.length_cons,
        List.length_nil] at hlen
      omega
    | .outArg id0, es =>
      simp only [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_outArg] at he
      simp only [CallArg.getInputExprs_cons_outArg] at hlen
      rcases ih es hlen e he with hmem | ⟨id, hid, heq⟩
      · exact Or.inl hmem
      · exact Or.inr ⟨id, by simp [CallArg.getLhs_cons_outArg, hid], heq⟩

/-- Each input expression after `replaceInArgs` is the replacement at that position or the bare
    variable the original arguments held there. -/
theorem CallArg.getInputExprs_replaceInArgs_getElem? :
    ∀ (args : List (CallArg Expression)) (newExprs : List Expression.Expr),
      newExprs.length = (CallArg.getInputExprs args).length →
      ∀ i : Nat, (CallArg.getInputExprs (CallArg.replaceInArgs args newExprs))[i]? = newExprs[i]? ∨
        ∃ id, (CallArg.getInputExprs args)[i]? = some
            (LExpr.fvar Core.coreLoc id none : Expression.Expr) ∧
          (CallArg.getInputExprs (CallArg.replaceInArgs args newExprs))[i]?
            = some (LExpr.fvar Core.coreLoc id none : Expression.Expr) := by
  intro args
  simp only [CallArg.replaceInArgs]
  induction args with
  | nil =>
    intro newExprs hlen i
    left
    simp only [CallArg.getInputExprs, Calls.getInputExprs, CallArg.replaceInArgs.go,
      List.filterMap_nil, List.getElem?_nil]
    simp only [CallArg.getInputExprs, Calls.getInputExprs, List.filterMap_nil, List.length_nil]
      at hlen
    rw [List.length_eq_zero_iff.mp hlen]
    simp
  | cons a rest ih =>
    intro newExprs hlen i
    match a, newExprs with
    | .inArg e0, e1 :: rest2 =>
      simp only [CallArg.getInputExprs_cons_inArg, List.length_cons] at hlen
      match i with
      | 0 => left; simp [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_inArg]
      | n + 1 =>
        rcases ih rest2 (by omega) n with hl | ⟨id, h1, h2⟩
        · left; simpa [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_inArg] using hl
        · refine Or.inr ⟨id, ?_, ?_⟩
          · simpa [CallArg.getInputExprs_cons_inArg] using h1
          · simpa [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_inArg] using h2
    | .inArg e0, [] =>
      simp only [CallArg.getInputExprs_cons_inArg, List.length_cons, List.length_nil] at hlen
      omega
    | .inoutArg id0, e1 :: rest2 =>
      simp only [CallArg.getInputExprs_cons_inoutArg, List.length_cons] at hlen
      match i with
      | 0 =>
        refine Or.inr ⟨id0, ?_, ?_⟩
        · simp [CallArg.getInputExprs_cons_inoutArg]
        · simp [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_inoutArg]
      | n + 1 =>
        rcases ih rest2 (by omega) n with hl | ⟨id, h1, h2⟩
        · left; simpa [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_inoutArg] using hl
        · refine Or.inr ⟨id, ?_, ?_⟩
          · simpa [CallArg.getInputExprs_cons_inoutArg] using h1
          · simpa [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_inoutArg] using h2
    | .inoutArg id0, [] =>
      simp only [CallArg.getInputExprs_cons_inoutArg, List.length_cons, List.length_nil] at hlen
      omega
    | .outArg id0, rest2 =>
      simp only [CallArg.getInputExprs_cons_outArg] at hlen
      rcases ih rest2 hlen i with hl | ⟨id, h1, h2⟩
      · left; simpa [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_outArg] using hl
      · refine Or.inr ⟨id, ?_, ?_⟩
        · simpa [CallArg.getInputExprs_cons_outArg] using h1
        · simpa [CallArg.replaceInArgs.go, CallArg.getInputExprs_cons_outArg] using h2

/-- Mapping type annotations over a command statement maps them over the
    command. -/
theorem mapStmtTys_cmd (f : LMonoTy → LMonoTy) (c : Command) :
    mapStmtTys f (.cmd c) = .cmd (mapCmdTys f c) := by
  simp only [mapStmtTys, Stmt.mapExpr]

/-- Mapping type annotations over a labeled block maps them over its body. -/
theorem mapStmtTys_block (f : LMonoTy → LMonoTy) (l : String) (bss : List Statement)
    (md : MetaData Expression) :
    mapStmtTys f (.block l bss md) = .block l (mapStmtsTys f bss) md := by
  simp only [mapStmtTys, mapStmtsTys, Stmt.mapExpr]

/-- Mapping type annotations over a conditional maps them over its condition
    and both branches. -/
theorem mapStmtTys_ite (f : LMonoTy → LMonoTy) (cond : ExprOrNondet Expression)
    (tss ess : List Statement) (md : MetaData Expression) :
    mapStmtTys f (.ite cond tss ess md) =
      .ite (cond.map (mapExprTys f ·)) (mapStmtsTys f tss) (mapStmtsTys f ess) md := by
  cases cond <;> simp only [mapStmtTys, mapStmtsTys, Stmt.mapExpr, ExprOrNondet.map]

/-- Mapping type annotations over a loop maps them over its guard, measure,
    invariants and body. -/
theorem mapStmtTys_loop (f : LMonoTy → LMonoTy) (g : ExprOrNondet Expression)
    (m : Option Expression.Expr) (i : List (String × Expression.Expr))
    (bss : List Statement) (md : MetaData Expression) :
    mapStmtTys f (.loop g m i bss md) =
      .loop (g.map (mapExprTys f ·)) (m.map (mapExprTys f ·))
        (i.map (fun (l, e) => (l, mapExprTys f e))) (mapStmtsTys f bss) md := by
  cases g <;> simp only [mapStmtTys, mapStmtsTys, Stmt.mapExpr, ExprOrNondet.map]

/-- Mapping type annotations leaves an exit unchanged. -/
theorem mapStmtTys_exit (f : LMonoTy → LMonoTy) (l : String)
    (md : MetaData Expression) :
    mapStmtTys f (.exit l md) = .exit l md := by
  simp only [mapStmtTys, Stmt.mapExpr]

/-- Mapping type annotations leaves a type declaration unchanged. -/
theorem mapStmtTys_typeDecl (f : LMonoTy → LMonoTy) (t : TypeConstructor)
    (md : MetaData Expression) :
    mapStmtTys f (.typeDecl t md) = .typeDecl t md := by
  simp only [mapStmtTys, Stmt.mapExpr]

/-- Mapping type annotations over the empty statement list gives the empty
    list. -/
theorem mapStmtsTys_nil (f : LMonoTy → LMonoTy) : mapStmtsTys f [] = [] := by
  simp only [mapStmtsTys, Block.mapExpr]

/-- Mapping type annotations over a statement list maps them over its head and
    its tail. -/
theorem mapStmtsTys_cons (f : LMonoTy → LMonoTy) (s : Statement) (rest : List Statement) :
    mapStmtsTys f (s :: rest) = mapStmtTys f s :: mapStmtsTys f rest := by
  simp only [mapStmtTys, mapStmtsTys, Block.mapExpr]

/-- Mapping the type annotations of a command by the identity leaves it unchanged. -/
theorem mapCmdTys_id (c : Command) : mapCmdTys id c = c := by
  have hid : mapExprTys (T := CoreLParams) id = id := Lambda.mapExprTys_id
  have hargs : ∀ args : List (CallArg Expression), args.map (CallArg.mapInput id) = args :=
    fun args => by
      conv => rhs; rw [← List.map_id args]
      exact List.map_congr_left fun a _ => by cases a <;> rfl
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      cases ty; cases e <;> simp [mapCmdTys, mapCmdWith, mapLTyTys, ExprOrNondet.map, hid]
    | set x e md => cases e <;> simp [mapCmdTys, mapCmdWith, ExprOrNondet.map, hid]
    | _ => simp [mapCmdTys, mapCmdWith, hid]
  | call n tyArgs args md =>
    cases tyArgs with
    | none => simp [mapCmdTys, mapCmdWith, hid, hargs]
    | some tys =>
      have htys : tys.map (mapLTyTys id) = tys := by
        conv => rhs; rw [← List.map_id tys]
        exact List.map_congr_left fun t _ => by cases t; rfl
      simp [mapCmdTys, mapCmdWith, hid, hargs, htys]

/-- Mapping the type annotations of a list of statements by the identity leaves it
    unchanged. -/
theorem mapStmtsTys_id (ss : List Statement) : mapStmtsTys id ss = ss := by
  induction ss using Block.mapExpr.induct (motive1 := fun s => mapStmtTys id s = s) with
  | case1 c => rw [mapStmtTys_cmd, mapCmdTys_id]
  | _ =>
    simp_all [mapStmtTys_block, mapStmtTys_ite, mapStmtTys_loop, mapStmtTys_exit,
      mapStmtTys_typeDecl, mapStmtsTys_nil, mapStmtsTys_cons, ExprOrNondet.map]

/-! ## No procedure call, one constructor at a time -/

/-- A list makes no call exactly when its head and its rest make none. -/
theorem noCalls_eq_cons (s : Statement) (rest : List Statement) :
    Statements.noCalls (s :: rest) = (Statement.noCalls s && Statements.noCalls rest) := by
  rw [Statements.noCalls, Imperative.Block.allSubstmts_cons]; rfl

/-- A block makes no call exactly when its body makes none. -/
theorem noCalls_eq_block (l : String) (ss : List Statement) (md : MetaData Expression) :
    Statement.noCalls (.block l ss md) = Statements.noCalls ss := by
  rw [Statement.noCalls, Imperative.Stmt.allSubstmts_block]; rfl

/-- A conditional makes no call exactly when neither arm makes one. -/
theorem noCalls_eq_ite (c : ExprOrNondet Expression) (ts es : List Statement)
    (md : MetaData Expression) :
    Statement.noCalls (.ite c ts es md) = (Statements.noCalls ts && Statements.noCalls es) := by
  rw [Statement.noCalls, Imperative.Stmt.allSubstmts_ite]; rfl

/-- A loop makes no call exactly when its body makes none. -/
theorem noCalls_eq_loop (g : ExprOrNondet Expression) (m : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (body : List Statement)
    (md : MetaData Expression) :
    Statement.noCalls (.loop g m invs body md) = Statements.noCalls body := by
  rw [Statement.noCalls, Imperative.Stmt.allSubstmts_loop]; rfl

/-- The empty statement list makes no procedure call. -/
theorem noCalls_nil : Statements.noCalls [] = true :=
  Imperative.Block.allSubstmts_nil _

/-- A list without calls has its head statement and its tail without calls. -/
theorem noCalls_cons {s : Statement} {rest : List Statement}
    (h : Statements.noCalls (s :: rest) = true) :
    Statement.noCalls s = true ∧ Statements.noCalls rest = true := by
  rwa [noCalls_eq_cons, Bool.and_eq_true] at h

/-- A statement without calls is a one-element list without calls. -/
theorem noCalls_singleton {s : Statement}
    (h : Statement.noCalls s = true) : Statements.noCalls [s] = true := by
  rw [noCalls_eq_cons, h, noCalls_nil, Bool.and_self]

/-- The body of a block without calls has none. -/
theorem noCalls_block {l : String} {ss : List Statement} {md : MetaData Expression}
    (h : Statement.noCalls (.block l ss md) = true) : Statements.noCalls ss = true := by
  rwa [noCalls_eq_block] at h

/-- Both arms of a conditional without calls have none. -/
theorem noCalls_ite {c : ExprOrNondet Expression} {ts es : List Statement}
    {md : MetaData Expression} (h : Statement.noCalls (.ite c ts es md) = true) :
    Statements.noCalls ts = true ∧ Statements.noCalls es = true := by
  rwa [noCalls_eq_ite, Bool.and_eq_true] at h

/-- The body of a loop without calls has none. -/
theorem noCalls_loop {g : ExprOrNondet Expression} {m : Option Expression.Expr}
    {invs : List (String × Expression.Expr)} {body : List Statement}
    {md : MetaData Expression} (h : Statement.noCalls (.loop g m invs body md) = true) :
    Statements.noCalls body = true := by
  rwa [noCalls_eq_loop] at h

/-- A command statement without calls carries a base command. -/
theorem exists_baseCmd_of_noCalls {c : Command} (h : Statement.noCalls (.cmd c) = true) :
    ∃ c' : Imperative.Cmd Expression, c = .cmd c' := by
  cases c with
  | cmd c' => exact ⟨c', rfl⟩
  | call n _ args md =>
    rw [Statement.noCalls, Imperative.Stmt.allSubstmts_cmd] at h; cases h

/-- Rewriting each `inArg` expression keeps the left-hand-side ids. -/
theorem CallArg.getLhs_map_congr (g : Expression.Expr → Expression.Expr)
    (args : List (CallArg Expression)) :
    CallArg.getLhs (args.map (CallArg.mapInput g)) = CallArg.getLhs args := by
  simp only [CallArg.getLhs, List.filterMap_map]
  congr 1
  funext a
  cases a <;> rfl

/-- Mapping call-argument types maps the call's input expressions. -/
theorem CallArg.getInputExprs_map_types (f : LMonoTy → LMonoTy)
    (args : List (CallArg Expression)) :
    CallArg.getInputExprs (args.map (CallArg.mapInput (mapExprTys f)))
      = (CallArg.getInputExprs args).map (mapExprTys f) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | inArg e =>
      simp only [List.map_cons, CallArg.mapInput, CallArg.getInputExprs_cons_inArg, ih]
    | inoutArg id =>
      simp only [List.map_cons, CallArg.mapInput, CallArg.getInputExprs_cons_inoutArg, ih]
      rw [mapExprTys, LExpr.replaceUserProvidedType, Option.map_none]
    | outArg id =>
      simp only [List.map_cons, CallArg.mapInput, CallArg.getInputExprs_cons_outArg, ih]

/-- Rewriting each `inArg` expression keeps the number of call inputs. -/
theorem CallArg.getInputExprs_length_map_mapInput (g : Expression.Expr → Expression.Expr)
    (args : List (CallArg Expression)) :
    (CallArg.getInputExprs (args.map (CallArg.mapInput g))).length
      = (CallArg.getInputExprs args).length := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    cases a <;>
      simp only [List.map_cons, CallArg.mapInput, CallArg.getInputExprs_cons_inArg,
        CallArg.getInputExprs_cons_inoutArg, CallArg.getInputExprs_cons_outArg,
        List.length_cons, ih]

/-- Rewriting each `inArg` expression rewrites the arguments passed for the input formals. -/
theorem CallArg.inputArgs_map_mapInput (g : Expression.Expr → Expression.Expr)
    (args : List (CallArg Expression)) :
    CallArg.inputArgs (args.map (CallArg.mapInput g))
      = (CallArg.inputArgs args).map (CallArg.mapInput g) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    cases a <;>
      simp only [List.map_cons, CallArg.mapInput, CallArg.inputArgs, List.filter_cons] at ih ⊢ <;>
      simp only [ite_true, ite_false, Bool.false_eq_true, List.map_cons, CallArg.mapInput, ih]

/-- Rewriting each `inArg` expression rewrites the arguments passed for the output formals. -/
theorem CallArg.resultArgs_map_mapInput (g : Expression.Expr → Expression.Expr)
    (args : List (CallArg Expression)) :
    CallArg.resultArgs (args.map (CallArg.mapInput g))
      = (CallArg.resultArgs args).map (CallArg.mapInput g) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    cases a <;>
      simp only [List.map_cons, CallArg.mapInput, CallArg.resultArgs, List.filter_cons] at ih ⊢ <;>
      simp only [ite_true, ite_false, Bool.false_eq_true, List.map_cons, CallArg.mapInput, ih]

/-- Replacing a call's `in` expressions changes only `inArg` expressions: the result agrees with
    the original once every `inArg` expression is rewritten to one constant. -/
theorem CallArg.replaceInArgs_map_mapInput_const (e0 : Expression.Expr)
    (args : List (CallArg Expression)) (es : List Expression.Expr) :
    (CallArg.replaceInArgs args es).map (CallArg.mapInput fun _ => e0)
      = args.map (CallArg.mapInput fun _ => e0) := by
  rw [CallArg.replaceInArgs]
  induction args generalizing es with
  | nil => rfl
  | cons a rest ih =>
    cases a <;> cases es <;>
      simp only [CallArg.replaceInArgs.go, List.map_cons, CallArg.mapInput, ih]

/-- Rewriting `inArg` expressions and then rewriting them all to a constant is rewriting them all
    to that constant. -/
theorem CallArg.map_mapInput_const (g : Expression.Expr → Expression.Expr) (e0 : Expression.Expr)
    (args : List (CallArg Expression)) :
    (args.map (CallArg.mapInput g)).map (CallArg.mapInput fun _ => e0)
      = args.map (CallArg.mapInput fun _ => e0) := by
  rw [List.map_map]
  congr 1
  funext a
  cases a <;> rfl

/-- Each call input is either an unannotated variable or satisfies the argument annotation check. -/
theorem CallArg.getInputExprs_annotations {A : LMonoTy → Bool}
    (args : List (CallArg Expression))
    (h : args.all fun
      | .inArg e => allExprTys A e
      | .inoutArg _ => true
      | .outArg _ => true) :
    ∀ e ∈ CallArg.getInputExprs args,
      (∃ m x, e = LExpr.fvar m x none) ∨ allExprTys A e = true := by
  induction args with
  | nil =>
    intro e he
    simp [CallArg.getInputExprs, Calls.getInputExprs] at he
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases a with
    | inArg e0 =>
      intro e he
      simp only [CallArg.getInputExprs, Calls.getInputExprs, List.filterMap_cons, List.mem_cons]
        at he
      rcases he with rfl | he
      · exact Or.inr h.1
      · exact ih h.2 e he
    | inoutArg x =>
      intro e he
      simp only [CallArg.getInputExprs, Calls.getInputExprs, List.filterMap_cons, List.mem_cons]
        at he
      rcases he with rfl | he
      · exact Or.inl ⟨Core.coreLoc, x, rfl⟩
      · exact ih h.2 e he
    | outArg x =>
      intro e he
      simp only [CallArg.getInputExprs, Calls.getInputExprs, List.filterMap_cons] at he
      exact ih h.2 e he

/-- Mapping expressions and types over a command keeps the variables it modifies. -/
theorem Command.modifiedVars_mapCmdWith (fe : Expression.Expr → Expression.Expr)
    (ft : LMonoTy → LMonoTy) (c : Command) :
    Command.modifiedVars (mapCmdWith fe ft c) = Command.modifiedVars c := by
  cases c with
  | cmd cc =>
    cases cc <;> simp [mapCmdWith, Command.modifiedVars, CmdExt.modifiedVars, Cmd.modifiedVars]
  | call pname tyArgs args md =>
    simp only [mapCmdWith, Command.modifiedVars]
    exact CallArg.getLhs_map_congr fe args

/-- Mapping expressions and types over a command keeps the variables it defines. -/
theorem Command.definedVars_mapCmdWith (fe : Expression.Expr → Expression.Expr)
    (ft : LMonoTy → LMonoTy) (c : Command) :
    Command.definedVars (mapCmdWith fe ft c) = Command.definedVars c := by
  cases c with
  | cmd cc =>
    cases cc <;> simp [mapCmdWith, Command.definedVars, CmdExt.definedVars, Cmd.definedVars]
  | call pname args md => simp [mapCmdWith, Command.definedVars, CmdExt.definedVars]

/-- Mapping expressions and types over a command keeps the procedure names it calls. -/
theorem CmdExt.calledProcedureNames_mapCmdWith (fe : Expression.Expr → Expression.Expr)
    (ft : LMonoTy → LMonoTy) (c : Command) :
    CmdExt.calledProcedureNames (mapCmdWith fe ft c) = CmdExt.calledProcedureNames c := by
  cases c with
  | cmd cc => cases cc <;> simp [mapCmdWith]
  | call pname args md => simp [mapCmdWith]

/-- Mapping expressions and types over a statement list keeps the variables it modifies. -/
theorem Block.modifiedVars_mapExpr_mapCmdWith (fe : Expression.Expr → Expression.Expr)
    (ft : LMonoTy → LMonoTy) (ss : List Statement) :
    Block.modifiedVars (Block.mapExpr fe (mapCmdWith fe ft) ss) = Block.modifiedVars ss := by
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      Stmt.modifiedVars (Stmt.mapExpr fe (mapCmdWith fe ft) s) = Stmt.modifiedVars s) with
  | case1 c =>
    simp only [Stmt.mapExpr, Stmt.modifiedVars]
    exact Command.modifiedVars_mapCmdWith fe ft c
  | _ => simp_all only [Stmt.mapExpr, Block.mapExpr, Stmt.modifiedVars, Block.modifiedVars]

/-- Mapping expressions and types over a statement list keeps the variables it defines. -/
theorem Block.definedVars_mapExpr_mapCmdWith (fe : Expression.Expr → Expression.Expr)
    (ft : LMonoTy → LMonoTy) (ss : List Statement) :
    ∀ b, Block.definedVars (Block.mapExpr fe (mapCmdWith fe ft) ss) b =
      Block.definedVars ss b := by
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      ∀ b, Stmt.definedVars (Stmt.mapExpr fe (mapCmdWith fe ft) s) b =
        Stmt.definedVars s b) with
  | case1 c =>
    simp only [Stmt.mapExpr, Stmt.definedVars]
    exact Command.definedVars_mapCmdWith fe ft c
  | _ => simp_all only [Stmt.mapExpr, Block.mapExpr, Stmt.definedVars, Block.definedVars,
      implies_true]

/-- Mapping expressions and types over a statement list keeps the procedure names it calls. -/
theorem Block.calledProcedureNames_mapExpr_mapCmdWith (fe : Expression.Expr → Expression.Expr)
    (ft : LMonoTy → LMonoTy) (ss : List Statement) :
    Statements.calledProcedureNames (Block.mapExpr fe (mapCmdWith fe ft) ss) =
      Statements.calledProcedureNames ss := by
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      Statement.calledProcedureNames (Stmt.mapExpr fe (mapCmdWith fe ft) s) =
        Statement.calledProcedureNames s) <;>
    simp_all only [Stmt.mapExpr, Block.mapExpr, Statement.calledProcedureNames_cmd,
      Statement.calledProcedureNames_block, Statement.calledProcedureNames_ite,
      Statement.calledProcedureNames_loop, Statements.calledProcedureNames_cons,
      CmdExt.calledProcedureNames_mapCmdWith]

/-- Rewriting command type annotations preserves the variables the command modifies. -/
theorem Command.modifiedVars_mapCmdTys (f : LMonoTy → LMonoTy) (c : Command) :
    Command.modifiedVars (mapCmdTys f c) = Command.modifiedVars c :=
  Command.modifiedVars_mapCmdWith _ _ c

/-- Rewriting command type annotations preserves the variables the command defines. -/
theorem Command.definedVars_mapCmdTys (f : LMonoTy → LMonoTy) (c : Command) :
    Command.definedVars (mapCmdTys f c) = Command.definedVars c :=
  Command.definedVars_mapCmdWith _ _ c

/-- Rewriting statement-list type annotations preserves the called procedure names. -/
theorem mapStmtsTys_calledProcedureNames (f : LMonoTy → LMonoTy) (ss : List Statement) :
    Statements.calledProcedureNames (mapStmtsTys f ss) = Statements.calledProcedureNames ss :=
  Block.calledProcedureNames_mapExpr_mapCmdWith _ _ ss

/-- Rewriting statement-list type annotations preserves the modified variables. -/
theorem mapStmtsTys_modifiedVars (f : LMonoTy → LMonoTy) (ss : List Statement) :
    Block.modifiedVars (mapStmtsTys f ss) = Block.modifiedVars ss :=
  Block.modifiedVars_mapExpr_mapCmdWith _ _ ss

/-- Rewriting statement-list type annotations preserves the defined variables. -/
theorem mapStmtsTys_definedVars (f : LMonoTy → LMonoTy) (ss : List Statement) :
    ∀ b, Block.definedVars (mapStmtsTys f ss) b = Block.definedVars ss b :=
  Block.definedVars_mapExpr_mapCmdWith _ _ ss

/-- Mapping a function that fixes every type over the type arguments of a call changes nothing. -/
private theorem mapTyArgs_fix (f : LMonoTy → LMonoTy) (hf : ∀ t, f t = t)
    (tyArgs : Option (List LTy)) :
    tyArgs.map (·.map (mapLTyTys f)) = tyArgs := by
  cases tyArgs with
  | none => rfl
  | some tys =>
    refine congrArg some (List.map_id'' (fun ty => ?_) tys)
    cases ty
    simp only [mapLTyTys, hf]

/-- Mapping functions that fix every expression and every type over a command changes
    nothing. -/
theorem mapCmdWith_id (fe : Expression.Expr → Expression.Expr) (ft : LMonoTy → LMonoTy)
    (hfe : ∀ e, fe e = e) (hft : ∀ t, ft t = t) (c : Command) : mapCmdWith fe ft c = c := by
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      cases ty
      simp only [mapCmdWith, mapLTyTys, hft, ExprOrNondet.map_id fe hfe]
    | set x e md => simp only [mapCmdWith, ExprOrNondet.map_id fe hfe]
    | assert l b md => simp only [mapCmdWith, hfe]
    | assume l b md => simp only [mapCmdWith, hfe]
    | cover l b md => simp only [mapCmdWith, hfe]
  | call pname tyArgs args md =>
    simp only [mapCmdWith]
    congr 1
    · exact mapTyArgs_fix ft hft tyArgs
    · refine List.map_id'' (fun a => ?_) args
      cases a <;> simp [CallArg.mapInput, hfe]

/-- Mapping functions that fix every expression and every type over a statement list changes
    nothing. -/
theorem Block.mapExpr_mapCmdWith_id (fe : Expression.Expr → Expression.Expr)
    (ft : LMonoTy → LMonoTy) (hfe : ∀ e, fe e = e) (hft : ∀ t, ft t = t)
    (ss : List Statement) : Block.mapExpr fe (mapCmdWith fe ft) ss = ss := by
  have hid : fe = id := funext hfe
  subst hid
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      Stmt.mapExpr id (mapCmdWith id ft) s = s) <;>
    simp_all [Stmt.mapExpr, Block.mapExpr, mapCmdWith_id id ft hfe hft]

/-- The expression of a deterministic initialization is among the command's read expressions. -/
theorem Statement.mem_cmdExprs_init_det {x : Expression.Ident} {ty : Expression.Ty}
    {e : Expression.Expr} {md : MetaData Expression} :
    e ∈ Statement.cmdExprs (.cmd (.init x ty (.det e) md)) := by
  simp only [Statement.cmdExprs, Cmd.readExprs, ExprOrNondet.toList, List.mem_singleton]

/-- The expression of a deterministic assignment is among the command's read expressions. -/
theorem Statement.mem_cmdExprs_set_det {x : Expression.Ident} {e : Expression.Expr}
    {md : MetaData Expression} :
    e ∈ Statement.cmdExprs (.cmd (.set x (.det e) md)) := by
  simp only [Statement.cmdExprs, Cmd.readExprs, ExprOrNondet.toList, List.mem_singleton]

/-- The condition of an assertion is among the command's read expressions. -/
theorem Statement.mem_cmdExprs_assert {l : String} {e : Expression.Expr}
    {md : MetaData Expression} : e ∈ Statement.cmdExprs (.cmd (.assert l e md)) := by
  simp only [Statement.cmdExprs, Cmd.readExprs, List.mem_singleton]

/-- The condition of an assumption is among the command's read expressions. -/
theorem Statement.mem_cmdExprs_assume {l : String} {e : Expression.Expr}
    {md : MetaData Expression} : e ∈ Statement.cmdExprs (.cmd (.assume l e md)) := by
  simp only [Statement.cmdExprs, Cmd.readExprs, List.mem_singleton]

/-- The condition of a cover is among the command's read expressions. -/
theorem Statement.mem_cmdExprs_cover {l : String} {e : Expression.Expr}
    {md : MetaData Expression} : e ∈ Statement.cmdExprs (.cmd (.cover l e md)) := by
  simp only [Statement.cmdExprs, Cmd.readExprs, List.mem_singleton]

section CollectStructure

variable {β : Type} (fe : Expression.Expr → List β) (ft : LMonoTy → List β)

/-- A command statement collects what its command collects. -/
theorem stmtCollect_cmd (c : Command) : stmtCollect fe ft (.cmd c) = cmdCollect fe ft c := by
  simp only [stmtCollect, stmtOwnCollect, List.append_nil]

/-- When `ft` collects nothing, a command collects only from the expressions it reads. -/
theorem cmdCollect_of_ft_nil (c : Command) :
    cmdCollect fe (fun _ => []) c = (Statement.cmdExprs c).flatMap fe := by
  have hnil : (CmdExt.initTypes c).flatMap
      (fun ty => (fun _ : LMonoTy => ([] : List β)) ty.toMonoTypeUnsafe) = [] :=
    List.flatMap_eq_nil_iff.mpr fun _ _ => rfl
  have hnilTy : (Statement.cmdTyArgs c).flatMap
      (fun ty => (fun _ : LMonoTy => ([] : List β)) ty.toMonoTypeUnsafe) = [] :=
    List.flatMap_eq_nil_iff.mpr fun _ _ => rfl
  simp only [cmdCollect, hnil, hnilTy, List.nil_append]

/-- A block collects what its body collects. -/
theorem stmtCollect_block (l : String) (bss : List Statement) (md : MetaData Expression) :
    stmtCollect fe ft (.block l bss md) = stmtsCollect fe ft bss := by
  simp only [stmtCollect, stmtOwnCollect, List.nil_append]

/-- A conditional collects from its guard and both branches. -/
theorem stmtCollect_ite (cond : ExprOrNondet Expression) (tss ess : List Statement)
    (md : MetaData Expression) :
    stmtCollect fe ft (.ite cond tss ess md) =
      cond.toList.flatMap fe ++ (stmtsCollect fe ft tss ++ stmtsCollect fe ft ess) := by
  simp only [stmtCollect, stmtOwnCollect]

/-- A loop collects from its guard, measure, invariants and body. -/
theorem stmtCollect_loop (g : ExprOrNondet Expression) (m : Option Expression.Expr)
    (i : List (String × Expression.Expr)) (body : List Statement) (md : MetaData Expression) :
    stmtCollect fe ft (.loop g m i body md) =
      (Statement.loopExprs g m i).flatMap fe ++ stmtsCollect fe ft body := by
  simp only [stmtCollect, stmtOwnCollect]

/-- The empty statement list collects nothing. -/
theorem stmtsCollect_nil : stmtsCollect fe ft [] = [] := by
  simp only [stmtsCollect]

/-- A statement list collects what its first statement and the rest collect. -/
theorem stmtsCollect_cons (s : Statement) (ss : List Statement) :
    stmtsCollect fe ft (s :: ss) = stmtCollect fe ft s ++ stmtsCollect fe ft ss := by
  simp only [stmtsCollect]

end CollectStructure

end

end Core
