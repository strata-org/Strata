/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.WF
import all Strata.Languages.Core.CallWF
import all Strata.Languages.Core.Program
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.StatementProps

/-! # Properties of well-formed calls

`callArgsError?_eq_none_iff`: `callArgsError?` accepts exactly the arguments that
match the procedure's signature with distinct result variables.
`callError?_eq_none_iff`: `callError?` accepts exactly the calls that satisfy
`WF.WFcallProp`. `illFormedCalls_eq_nil_iff`: `illFormedCalls` finds nothing exactly
when every call of the program is well-formed (`Program.callsWellFormed`).
`WF.WFcallProp.of_argsMatch`: a call to a declared procedure is well-formed
when its arguments match the signature and its result variables are distinct.
-/

namespace Core

open Imperative

public section

/-- Every call in `p` is well-formed. -/
@[expose] def Program.callsWellFormed (p : Program) : Prop :=
  ∀ c ∈ p.callSites, WF.WFcallProp p c.procName c.args

/-! ## Agreement with `WF.WFcallProp` -/

/-- `aliasedResultsMessage?` finds nothing exactly when the result variables are
    distinct. -/
private theorem aliasedResultsMessage?_eq_none_iff (procName : String)
    (args : List (CallArg Expression)) :
    aliasedResultsMessage? procName args = none ↔ (CallArg.getLhs args).Nodup := by
  simp only [aliasedResultsMessage?, Option.map_eq_none_iff, List.find?_eq_none,
    decide_eq_true_eq, Nat.not_lt]
  rw [List.nodup_iff_count]
  constructor
  · intro h a
    by_cases ha : a ∈ CallArg.getLhs args
    · simpa [List.count_eq_length_filter] using h a ha
    · simp [List.count_eq_zero_of_not_mem ha]
  · intro h x _
    simpa [List.count_eq_length_filter] using h x

/-- `inputMismatchMessage?` finds nothing exactly when every input argument matches
    its formal. -/
private theorem inputMismatchMessage?_eq_none_iff (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) :
    inputMismatchMessage? procName proc args = none ↔
      ∀ xa ∈ proc.header.inputs.keys.zip (CallArg.inputArgs args),
        WF.inputArgMatches proc.header.outputs.keys (CallArg.getLhs args) xa.1 xa.2 = true := by
  simp [inputMismatchMessage?]

/-- `outputMismatchMessage?` finds nothing exactly when every result argument matches
    its formal. -/
private theorem outputMismatchMessage?_eq_none_iff (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) :
    outputMismatchMessage? procName proc args = none ↔
      ∀ zr ∈ proc.header.outputs.keys.zip (CallArg.resultArgs args),
        WF.outputArgMatches proc.header.inputs.keys zr.1 zr.2 = true := by
  simp [outputMismatchMessage?]

/-- `callArgsError?` finds nothing exactly when the arguments match the procedure's
    signature and the result variables are distinct. -/
theorem callArgsError?_eq_none_iff (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) :
    callArgsError? procName proc args = none ↔
      WF.ArgsMatchSignature proc args ∧ (CallArg.getLhs args).Nodup := by
  simp only [callArgsError?]
  by_cases h1 : (CallArg.getInputExprs args).length = proc.header.inputs.length
  · by_cases h2 : (CallArg.getLhs args).length = proc.header.outputs.length
    · simp only [h1, h2, ne_eq, not_true_eq_false, ↓reduceIte]
      rw [← aliasedResultsMessage?_eq_none_iff procName args]
      have hin := inputMismatchMessage?_eq_none_iff procName proc args
      have hout := outputMismatchMessage?_eq_none_iff procName proc args
      constructor
      · intro h
        split at h
        · simp at h
        · rename_i hi
          split at h
          · simp at h
          · rename_i ho
            exact ⟨⟨h1, h2, hin.mp hi, hout.mp ho⟩, h⟩
      · intro ⟨hm, hn⟩
        rw [hin.mpr hm.inputsMatch, hout.mpr hm.outputsMatch]
        exact hn
    · simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
        reduceCtorEq, false_iff]
      exact fun h => h2 h.1.resultCount
  · simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    exact fun h => h1 h.1.inputCount

/-- A call to a declared procedure is well-formed when its arguments match the
    procedure's signature and its result variables are distinct. -/
theorem WF.WFcallProp.of_argsMatch {p : Program} {procName : String}
    {proc : Procedure} {args : List (CallArg Expression)}
    (hfind : Program.Procedure.find? p procName = some proc)
    (hmatch : WF.ArgsMatchSignature proc args)
    (hnodup : (CallArg.getLhs args).Nodup) :
    WF.WFcallProp p procName args := {
  defined := by simp [hfind]
  argsMatch := fun h => by rw [hfind] at h; cases h; exact hmatch
  lhsWF := hnodup
  wfargs := List.Forall_mem_iff.mpr fun _ _ => ⟨⟩ }

/-- `callError?` accepts exactly the well-formed calls. -/
theorem callError?_eq_none_iff (p : Program) (procName : String)
    (args : List (CallArg Expression)) :
    callError? p procName args = none ↔ WF.WFcallProp p procName args := by
  unfold callError?
  split
  · rename_i hfind
    simp only [reduceCtorEq, false_iff]
    intro h
    simpa [hfind] using h.defined
  · rename_i proc hfind
    rw [callArgsError?_eq_none_iff]
    constructor
    · intro ⟨hm, hnodup⟩
      exact WF.WFcallProp.of_argsMatch hfind hm hnodup
    · intro h
      exact ⟨h.argsMatch hfind, h.lhsWF⟩

/-- `illFormedCalls` finds nothing exactly when every call is well-formed. -/
@[simp] theorem illFormedCalls_eq_nil_iff (p : Program) :
    illFormedCalls p = [] ↔ p.callsWellFormed := by
  simp only [illFormedCalls, List.filterMap_eq_nil_iff, Option.map_eq_none_iff,
    Program.callsWellFormed]
  constructor
  · intro h c hc
    exact (callError?_eq_none_iff p c.procName c.args).mp (h c hc)
  · intro h c hc
    exact (callError?_eq_none_iff p c.procName c.args).mpr (h c hc)

/-- A call's arguments match a procedure's signature exactly when they do after rewriting each
    `inArg` expression: matching depends only on each argument's mode and in-out variable. -/
theorem WF.ArgsMatchSignature.map_mapInput_iff (g : Expression.Expr → Expression.Expr)
    (proc : Procedure) (args : List (CallArg Expression)) :
    WF.ArgsMatchSignature proc (args.map (CallArg.mapInput g)) ↔
      WF.ArgsMatchSignature proc args := by
  have hin : ∀ (o l : List Expression.Ident) x a,
      WF.inputArgMatches o l x (CallArg.mapInput g a) = WF.inputArgMatches o l x a := by
    intro o l x a
    cases a with
    | inArg e =>
      show WF.inputArgMatches o l x (.inArg (g e)) = WF.inputArgMatches o l x (.inArg e)
      unfold WF.inputArgMatches
      cases o.idxOf? x <;> rfl
    | inoutArg v => rfl
    | outArg v => rfl
  have hout : ∀ (i : List Expression.Ident) z a,
      WF.outputArgMatches i z (CallArg.mapInput g a) = WF.outputArgMatches i z a := by
    intro i z a
    cases a <;> rfl
  have hlhs := CallArg.getLhs_map_congr g args
  constructor
  · intro h
    refine ⟨?_, hlhs ▸ h.resultCount, ?_, ?_⟩
    · rw [← CallArg.getInputExprs_length_map_mapInput g]
      exact h.inputCount
    · intro xa hxa
      have hmatch := h.inputsMatch (xa.1, CallArg.mapInput g xa.2)
      rw [CallArg.inputArgs_map_mapInput, List.zip_map_right, hlhs] at hmatch
      rw [← hin]
      exact hmatch (List.mem_map.mpr ⟨xa, hxa, rfl⟩)
    · intro zr hzr
      have hmatch := h.outputsMatch (zr.1, CallArg.mapInput g zr.2)
      rw [CallArg.resultArgs_map_mapInput, List.zip_map_right] at hmatch
      rw [← hout]
      exact hmatch (List.mem_map.mpr ⟨zr, hzr, rfl⟩)
  · intro h
    refine ⟨?_, hlhs ▸ h.resultCount, ?_, ?_⟩
    · rw [CallArg.getInputExprs_length_map_mapInput g]
      exact h.inputCount
    · intro xa hxa
      rw [CallArg.inputArgs_map_mapInput, List.zip_map_right] at hxa
      obtain ⟨ya, hya, rfl⟩ := List.mem_map.mp hxa
      simp only [Prod.map_fst, Prod.map_snd, id_eq, hin, hlhs]
      exact h.inputsMatch ya hya
    · intro zr hzr
      rw [CallArg.resultArgs_map_mapInput, List.zip_map_right] at hzr
      obtain ⟨yr, hyr, rfl⟩ := List.mem_map.mp hzr
      simp only [Prod.map_fst, Prod.map_snd, id_eq, hout]
      exact h.outputsMatch yr hyr

/-- A call's arguments match the signature of a procedure with the same input and output names
    as one whose signature they match. -/
theorem WF.ArgsMatchSignature.of_keys_eq {q1 q2 : Procedure} {args : List (CallArg Expression)}
    (hm : WF.ArgsMatchSignature q1 args) (hinKeys : q1.header.inputs.keys = q2.header.inputs.keys)
    (houtKeys : q1.header.outputs.keys = q2.header.outputs.keys) :
    WF.ArgsMatchSignature q2 args := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm.inputCount]
    simpa using congrArg List.length hinKeys
  · rw [hm.resultCount]
    simpa using congrArg List.length houtKeys
  · rw [← hinKeys, ← houtKeys]
    exact hm.inputsMatch
  · rw [← hinKeys, ← houtKeys]
    exact hm.outputsMatch

/-- A well-formed call stays well formed when its callee is replaced by a procedure with the same
    parameter names and its arguments by ones with the same modes and result variables (equal
    after rewriting every `inArg` expression to one constant). -/
theorem WF.WFcallProp.transfer {P1 P2 : Program} {nm : String} {q1 q2 : Procedure}
    {args args' : List (CallArg Expression)} (e0 : Expression.Expr)
    (h : WF.WFcallProp P1 nm args)
    (hq1 : Program.Procedure.find? P1 nm = some q1) (hq2 : Program.Procedure.find? P2 nm = some q2)
    (hinKeys : q1.header.inputs.keys = q2.header.inputs.keys)
    (houtKeys : q1.header.outputs.keys = q2.header.outputs.keys)
    (hshape : args'.map (CallArg.mapInput fun _ => e0)
      = args.map (CallArg.mapInput fun _ => e0)) :
    WF.WFcallProp P2 nm args' := by
  have hlhs : CallArg.getLhs args' = CallArg.getLhs args := by
    rw [← CallArg.getLhs_map_congr (fun _ => e0) args', hshape, CallArg.getLhs_map_congr]
  have hm1 : WF.ArgsMatchSignature q1 args := h.argsMatch hq1
  have hm2 : WF.ArgsMatchSignature q1 args' := by
    rw [← WF.ArgsMatchSignature.map_mapInput_iff (fun _ => e0), hshape,
      WF.ArgsMatchSignature.map_mapInput_iff]
    exact hm1
  exact WF.WFcallProp.of_argsMatch hq2 (hm2.of_keys_eq hinKeys houtKeys) (hlhs ▸ h.lhsWF)

/-- A well-formed call stays well formed when each of its `inArg` expressions is rewritten. -/
theorem WF.WFcallProp.map_mapInput {P : Program} {nm : String} {args : List (CallArg Expression)}
    (g : Expression.Expr → Expression.Expr) (h : WF.WFcallProp P nm args) :
    WF.WFcallProp P nm (args.map (CallArg.mapInput g)) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h.defined
  exact WF.WFcallProp.transfer default h hq hq rfl rfl (CallArg.map_mapInput_const g default args)

/-- A command's calls stay well formed when it is replaced by a command whose calls are its calls
    with the type arguments rewritten by `ft` and each `inArg` expression rewritten by `g`. -/
theorem Command.callsWellFormed_mapInput {P : Program} (g : Expression.Expr → Expression.Expr)
    (ft : Option (List Expression.Ty) → Option (List Expression.Ty)) {y y' : Command}
    (hsites : Command.callSites y' =
      (Command.callSites y).map fun cs =>
        { cs with tyArgs := ft cs.tyArgs, args := cs.args.map (CallArg.mapInput g) })
    (h : ∀ cs ∈ Command.callSites y, WF.WFcallProp P cs.procName cs.args) :
    ∀ cs ∈ Command.callSites y', WF.WFcallProp P cs.procName cs.args := by
  rw [hsites]
  intro cs hcs
  obtain ⟨cs₀, hmem, rfl⟩ := List.mem_map.mp hcs
  exact WF.WFcallProp.map_mapInput g (h cs₀ hmem)

/-- A well-formed call stays well formed in a program that looks its callee up the same way. -/
private theorem WF.WFcallProp.of_find?_eq {P1 P2 : Program} {nm : String}
    {args : List (CallArg Expression)}
    (hfind : Program.Procedure.find? P2 nm = Program.Procedure.find? P1 nm)
    (h : WF.WFcallProp P1 nm args) : WF.WFcallProp P2 nm args := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h.defined
  exact WF.WFcallProp.of_argsMatch (hfind.trans hq) (h.argsMatch hq) h.lhsWF

/-- A program with the same procedures as one whose calls are well formed, in the same order,
    has well-formed calls: its calls are the same, and each callee is found the same way. -/
theorem Program.callsWellFormed_of_procs_eq {p p' : Program}
    (hprocs : p'.decls.filter Decl.isProc = p.decls.filter Decl.isProc)
    (h : p.callsWellFormed) : p'.callsWellFormed := by
  intro c hc
  rw [Program.callSites_of_procs_eq hprocs] at hc
  exact WF.WFcallProp.of_find?_eq (Program.Procedure.find?_of_procs_eq hprocs _) (h c hc)

/-- When each output formal agrees in kind with the result argument it is paired with, the two
    agree at every position. -/
theorem WF.outputArgMatches_of_zip {inputs : List Expression.Ident}
    {zs : List Expression.Ident} {rs : List (CallArg Expression)}
    (h : ∀ zr ∈ zs.zip rs, WF.outputArgMatches inputs zr.1 zr.2 = true) :
    ∀ (k : Nat) (z : Expression.Ident) (r : CallArg Expression), zs[k]? = some z →
      rs[k]? = some r → WF.outputArgMatches inputs z r = true :=
  fun _ z r hz hr =>
    h (z, r) (List.mem_iff_getElem?.2 ⟨_, List.getElem?_zip_eq_some.2 ⟨hz, hr⟩⟩)

/-- When each output formal agrees in kind with the result argument at its position, the output
    formal at the position of an `out` argument is an output-only formal, at the position of
    that `out` variable among the `out` variables. -/
theorem WF.outArg_aligned (inputs : List Expression.Ident) :
    ∀ (zs : List Expression.Ident) (rs : List (CallArg Expression)),
    (∀ (k : Nat) (z : Expression.Ident) (r : CallArg Expression), zs[k]? = some z →
      rs[k]? = some r → WF.outputArgMatches inputs z r = true) →
    ∀ (k : Nat) (z w : Expression.Ident), zs[k]? = some z →
      rs[k]? = some (CallArg.outArg w) →
      ∃ j : Nat, (zs.filter (fun x => !inputs.contains x))[j]? = some z ∧
        (CallArg.getOutArgs rs)[j]? = some w := by
  intro zs
  induction zs with
  | nil => intro rs _ k z w hz; simp only [List.getElem?_nil, reduceCtorEq] at hz
  | cons z0 zs ih =>
    intro rs hm k z w hz hr
    cases rs with
    | nil => simp only [List.getElem?_nil, reduceCtorEq] at hr
    | cons r0 rs =>
      have hm0 := hm 0 z0 r0 rfl rfl
      have hm' : ∀ (k : Nat) (z : Expression.Ident) (r : CallArg Expression), zs[k]? = some z →
          rs[k]? = some r → WF.outputArgMatches inputs z r = true :=
        fun k z r hz hr => hm (k + 1) z r hz hr
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hz hr
        subst hz hr
        refine ⟨0, ?_, ?_⟩
        · simp only [WF.outputArgMatches] at hm0
          rw [List.filter_cons_of_pos (p := fun x => !inputs.contains x) hm0]
          rfl
        · simp only [CallArg.getOutArgs, List.filterMap_cons]
          rfl
      | succ k =>
        simp only [List.getElem?_cons_succ] at hz hr
        obtain ⟨j, hj1, hj2⟩ := ih rs hm' k z w hz hr
        cases r0 with
        | inArg ex => simp only [WF.outputArgMatches, Bool.false_eq_true] at hm0
        | inoutArg id =>
          simp only [WF.outputArgMatches] at hm0
          refine ⟨j, ?_, ?_⟩
          · have hnot : ¬(!inputs.contains z0) = true := by rw [hm0]; decide
            rw [List.filter_cons_of_neg (p := fun x => !inputs.contains x) hnot]
            exact hj1
          · simpa only [CallArg.getOutArgs, List.filterMap_cons] using hj2
        | outArg id =>
          simp only [WF.outputArgMatches] at hm0
          refine ⟨j + 1, ?_, ?_⟩
          · rw [List.filter_cons_of_pos (p := fun x => !inputs.contains x) hm0]
            simpa only [List.getElem?_cons_succ] using hj1
          · simpa only [CallArg.getOutArgs, List.filterMap_cons,
              List.getElem?_cons_succ] using hj2

/-- When there are as many result arguments as output formals and each output formal agrees in
    kind with the result argument it is paired with, there are as many `out` arguments as
    output-only formals. -/
theorem WF.outputOnly_length (inputs : List Expression.Ident) :
    ∀ (zs : List Expression.Ident) (rs : List (CallArg Expression)),
    zs.length = rs.length →
    (∀ zr ∈ zs.zip rs, WF.outputArgMatches inputs zr.1 zr.2 = true) →
    (zs.filter (fun x => !inputs.contains x)).length = (CallArg.getOutArgs rs).length := by
  intro zs
  induction zs with
  | nil =>
    intro rs hlen _
    cases rs with
    | nil => rfl
    | cons =>
      exfalso
      simp only [List.length_nil, List.length_cons] at hlen
      omega
  | cons z zs ih =>
    intro rs hlen hm
    cases rs with
    | nil =>
      exfalso
      simp only [List.length_nil, List.length_cons] at hlen
      omega
    | cons r rs =>
      have hhead : (z, r) ∈ (z :: zs).zip (r :: rs) := by
        simp only [List.zip_cons_cons, List.mem_cons, true_or]
      have hm0 := hm (z, r) hhead
      have hm' : ∀ zr ∈ zs.zip rs, WF.outputArgMatches inputs zr.1 zr.2 = true := by
        intro zr hzr
        have htail : zr ∈ (z :: zs).zip (r :: rs) := by
          simp only [List.zip_cons_cons, List.mem_cons]
          exact .inr hzr
        exact hm zr htail
      have hlen' : zs.length = rs.length := by
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        exact hlen
      have hrec := ih rs hlen' hm'
      cases r with
      | inArg ex => simp only [WF.outputArgMatches, Bool.false_eq_true] at hm0
      | inoutArg id =>
        simp only [WF.outputArgMatches] at hm0
        have hnot : ¬(!inputs.contains z) = true := by rw [hm0]; decide
        rw [List.filter_cons_of_neg (p := fun x => !inputs.contains x) hnot]
        simpa only [CallArg.getOutArgs, List.filterMap_cons] using hrec
      | outArg id =>
        simp only [WF.outputArgMatches] at hm0
        rw [List.filter_cons_of_pos (p := fun x => !inputs.contains x) hm0]
        simpa only [CallArg.getOutArgs, List.filterMap_cons, List.length_cons,
          Nat.add_right_cancel_iff] using hrec

end -- public section

end Core
