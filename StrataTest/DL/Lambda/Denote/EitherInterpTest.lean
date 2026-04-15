/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.IntBoolFactory

/-!
## Test: Consistent Interpretation for a Polymorphic Either Datatype

We define a polymorphic `Either a b` datatype with constructors `Left` and
`Right`, the eliminator from `genBlockFactory`, plus `Int.Gt` (concreteEval)
and a function `gt'` with a body that calls `Int.Gt`.

The factory exercises three kinds of consistency:
- **Body consistency**: `gt'` has a body (`Int.Gt(x, y)`)
- **Eval consistency**: `Either$Elim` and `Int.Gt` have `concreteEval`
- **Constructor consistency**: `Left` and `Right` are constructors
-/

namespace Lambda

-- Use trivial metadata
private abbrev TP : LExprParams := ⟨Unit, Unit⟩

/-! ### Sort size measure for well-founded recursion -/

private def LSort.totalSize : LSort → Nat
  | .tcons _ args => 1 + args.foldl (fun acc s => acc + s.totalSize) 0
  | .bitvec _ => 1

private theorem foldl_totalSize_mono (acc : Nat) (xs : List LSort) :
    acc ≤ xs.foldl (fun a s => a + s.totalSize) acc := by
  induction xs generalizing acc with
  | nil => simp [List.foldl]
  | cons x xs ih => simp [List.foldl]; exact Nat.le_trans (Nat.le_add_right _ _) (ih _)

private theorem totalSize_mem_foldl {s : LSort} {args : List LSort} (acc : Nat)
    (h : s ∈ args) : s.totalSize + acc ≤ args.foldl (fun a x => a + x.totalSize) acc := by
  induction args generalizing acc with
  | nil => contradiction
  | cons x xs ih =>
    simp [List.foldl]
    cases h with
    | head =>
      have : acc + s.totalSize ≤ List.foldl (fun a x => a + x.totalSize) (acc + s.totalSize) xs :=
        foldl_totalSize_mono _ _
      omega
    | tail _ h =>
      have := ih (acc + x.totalSize) h
      omega

/-! ### Type constructor interpretation via well-founded recursion -/

/-- Helper: denote a sort using the Either-aware interpretation.
    Recurses on totalSize to break the tcInterp/SortDenote circularity. -/
private def denoteSort : LSort → Type
  | .tcons "bool" []      => Bool
  | .tcons "int" []       => Int
  | .tcons "real" []      => Rat
  | .tcons "string" []    => String
  | .bitvec n             => BitVec n
  | .tcons "arrow" [a, b] => denoteSort a → denoteSort b
  | .tcons "Either" [a, b] => Sum (denoteSort a) (denoteSort b)
  | .tcons _ _            => Unit
termination_by s => s.totalSize
decreasing_by all_goals simp_all [LSort.totalSize, List.foldl]; omega

/-- Type constructor interpretation: delegates to denoteSort for "Either",
    Unit for everything else. -/
private def eitherTcInterp : TyConstrInterp :=
  fun name args =>
    match name, args with
    | "Either", [a, b] => Sum (denoteSort a) (denoteSort b)
    | _, _ => Unit

private def denoteSort_default (s : LSort) : denoteSort s := by
  unfold denoteSort
  split <;> try exact default
  · rename_i a b; exact fun _ => denoteSort_default b
  · rename_i a b; exact Sum.inl (denoteSort_default a)
termination_by s.totalSize
decreasing_by all_goals simp_all [LSort.totalSize, List.foldl]; omega

private instance : TyConstrInterp.AllInhabited eitherTcInterp where
  inhabited := by
    intro name args
    simp only [eitherTcInterp]
    split
    · rename_i a b; exact ⟨Sum.inl (denoteSort_default a)⟩
    · exact ⟨()⟩

/-! ### Datatype and Factory -/

private def leftConstr : LConstr Unit :=
  { name := ⟨"Left", ()⟩, args := [(⟨"x", ()⟩, .ftvar "a")] }

private def rightConstr : LConstr Unit :=
  { name := ⟨"Right", ()⟩, args := [(⟨"y", ()⟩, .ftvar "b")] }

private def eitherDT : LDatatype Unit :=
  { name := "Either", typeArgs := ["a", "b"],
    constrs := [leftConstr, rightConstr], constrs_ne := by decide }

private def eitherBlock : MutualDatatype Unit := [eitherDT]

private def intGtFunc' : LFunc TP := (intGtFunc (T := TP)).func

/-- `gt' : int → int → bool` with body `Int.Gt(x, y)`.
    Tests body consistency: the opInterp for gt' must match the denotation
    of its body, which calls Int.Gt on its two fvar arguments. -/
private def gt'Func : LFunc TP :=
  let x : Identifier Unit := ⟨"x", ()⟩
  let y : Identifier Unit := ⟨"y", ()⟩
  let intTy : LMonoTy := .tcons "int" []
  let boolTy : LMonoTy := .tcons "bool" []
  let gtFullTy : LMonoTy := .arrow intTy (.arrow intTy boolTy)
  { name := ⟨"gt'", ()⟩
    typeArgs := []
    inputs := [(x, intTy), (y, intTy)]
    output := boolTy
    body := some (LExpr.app () (LExpr.app () (LExpr.op () ⟨"Int.Gt", ()⟩ (some gtFullTy))
                              (LExpr.fvar () x (some intTy)))
                    (LExpr.fvar () y (some intTy))) }

/-- Factory with: eliminator + constructors from genBlockFactory, Int.Gt, and gt'. -/
private def eitherFactory : @Factory TP :=
  let elims := elimFuncs (T := TP) eitherBlock default
  let constrs := eitherBlock.flatMap (fun d => d.constrs.map (fun c => constrFunc (T := TP) c d))
  match (Factory.default.tryAddAll (elims ++ constrs).toArray : Except _ (@Factory TP)) with
  | .ok f =>
    match f.tryPush intGtFunc' with
    | .ok f' =>
      match f'.tryPush gt'Func with
      | .ok f'' => f''
      | .error _ => f'
    | .error _ => f
  | .error _ => Factory.default

/-! ### Bridging SortDenote and denoteSort -/

/-- `SortDenote eitherTcInterp` and `denoteSort` compute the same type
    for every sort. -/
private theorem sortDenote_eq_denoteSort : (s : LSort) →
    SortDenote eitherTcInterp s = denoteSort s := by
  intro s
  induction s using LSort.ind with
  | hbitvec n => unfold SortDenote denoteSort; rfl
  | htcons name args ih =>
    unfold SortDenote
    split
    · -- bool
      rename_i heq; cases heq; simp only [denoteSort]
    · -- int
      rename_i heq; cases heq; simp only [denoteSort]
    · -- real
      rename_i heq; cases heq; simp only [denoteSort]
    · -- string
      rename_i heq; cases heq; simp only [denoteSort]
    · -- bitvec: impossible, tcons ≠ bitvec
      rename_i heq; cases heq
    · -- arrow
      rename_i a b heq; cases heq
      simp only [denoteSort]
      have ha := ih a (by simp)
      have hb := ih b (by simp)
      rw [ha, hb]
    · -- default (catch-all for SortDenote = tcInterp)
      rename_i h_not_bool h_not_int h_not_real h_not_string h_not_arrow heq
      cases heq
      unfold denoteSort eitherTcInterp
      split <;> first | rfl | simp_all

/-! ### Operator interpretation -/

/-- Default value for any sort under eitherTcInterp. -/
private def sortDefault (s : LSort) : SortDenote eitherTcInterp s :=
  (SortDenote.inhabited eitherTcInterp
    (TyConstrInterp.AllInhabited.inhabited (self := inferInstance)) s).default

/-- Interpretation of `Left : a → Either a b`. -/
private def leftInterp (a b : LSort) :
    SortDenote eitherTcInterp a → SortDenote eitherTcInterp (.tcons "Either" [a, b]) :=
  fun x => by
    unfold SortDenote eitherTcInterp
    exact Sum.inl ((sortDenote_eq_denoteSort a).mp x)

/-- Interpretation of `Right : b → Either a b`. -/
private def rightInterp (a b : LSort) :
    SortDenote eitherTcInterp b → SortDenote eitherTcInterp (.tcons "Either" [a, b]) :=
  fun x => by
    unfold SortDenote eitherTcInterp
    exact Sum.inr ((sortDenote_eq_denoteSort b).mp x)

/-- Interpretation of `Int.Gt : Int → Int → Bool`. -/
private def intGtInterp : Int → Int → Bool := (· > ·)

/-- Eliminator interpretation: `Either$Elim(x, f, g) = match x with inl a => f a | inr b => g b`. -/
private def elimInterp (a b ret : LSort) :
    SortDenote eitherTcInterp (.tcons "Either" [a, b]) →
    (SortDenote eitherTcInterp a → SortDenote eitherTcInterp ret) →
    (SortDenote eitherTcInterp b → SortDenote eitherTcInterp ret) →
    SortDenote eitherTcInterp ret :=
  fun x f g => by
    unfold SortDenote eitherTcInterp at x
    exact match x with
    | .inl v => f ((sortDenote_eq_denoteSort a).symm ▸ v)
    | .inr v => g ((sortDenote_eq_denoteSort b).symm ▸ v)

/-- Operator interpretation for the Either factory.
    Maps each function name to its semantic meaning at the given sort. -/
private def eitherOpInterp : OpInterp eitherTcInterp :=
  fun name sort => by
    revert sort
    match name with
    | "Left" => intro sort; exact match sort with
      | .tcons "arrow" [a, .tcons "Either" [a', b]] =>
        if h : a = a' then h ▸ leftInterp a b
        else sortDefault _
      | s => sortDefault s
    | "Right" => intro sort; exact match sort with
      | .tcons "arrow" [b, .tcons "Either" [a, b']] =>
        if h : b = b' then h ▸ rightInterp a b
        else sortDefault _
      | s => sortDefault s
    | "Either$Elim" => intro sort; exact match sort with
      | .tcons "arrow" [.tcons "Either" [a, b],
          .tcons "arrow" [.tcons "arrow" [a', ret],
            .tcons "arrow" [.tcons "arrow" [b', ret'], ret'']]] =>
        if ha : a = a' then if hb : b = b' then if hr : ret = ret' then
          if hr2 : ret = ret'' then
            fun x f g => hr2 ▸ elimInterp a b ret x (ha ▸ f) (hb ▸ hr ▸ g)
          else sortDefault _
        else sortDefault _ else sortDefault _ else sortDefault _
      | s => sortDefault s
    | "Int.Gt" => intro sort; exact match sort with
      | .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] =>
        intGtInterp
      | s => sortDefault s
    | "gt'" => intro sort; exact match sort with
      | .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] =>
        intGtInterp
      | s => sortDefault s
    | _ => intro sort; exact sortDefault sort

/-! ### Consistency proofs -/

private theorem eitherFactory_names :
    eitherFactory.toArray.map (·.name.name) =
    #["Either$Elim", "Left", "Right", "Int.Gt", "gt'"] := by native_decide

private theorem eitherFactory_mem (f : String) (hf : f ∈ eitherFactory) :
    f = "Either$Elim" ∨ f = "Left" ∨ f = "Right" ∨ f = "Int.Gt" ∨ f = "gt'" := by
  rw [Factory.mem_iff_mem_names, eitherFactory_names] at hf
  simp [Array.mem_def] at hf
  rcases hf with h | h | h | h | h <;> simp_all

-- Membership lemmas
private def elim_mem : "Either$Elim" ∈ eitherFactory := by native_decide
private def left_mem : "Left" ∈ eitherFactory := by native_decide
private def right_mem : "Right" ∈ eitherFactory := by native_decide
private def intGt_mem : "Int.Gt" ∈ eitherFactory := by native_decide
private def gt'_mem : "gt'" ∈ eitherFactory := by native_decide

-- Body facts
private theorem elim_no_body : (eitherFactory["Either$Elim"]'elim_mem).body = none := by native_decide
private theorem left_no_body : (eitherFactory["Left"]'left_mem).body = none := by native_decide
private theorem right_no_body : (eitherFactory["Right"]'right_mem).body = none := by native_decide
private theorem intGt_no_body : (eitherFactory["Int.Gt"]'intGt_mem).body = none := by native_decide

-- concreteEval facts
private theorem left_no_ceval : (eitherFactory["Left"]'left_mem).concreteEval.isNone = true := by native_decide
private theorem right_no_ceval : (eitherFactory["Right"]'right_mem).concreteEval.isNone = true := by native_decide
private theorem gt'_no_ceval : (eitherFactory["gt'"]'gt'_mem).concreteEval.isNone = true := by native_decide

-- gt' field lemmas
private theorem gt'_name : (eitherFactory["gt'"]'gt'_mem).name.name = "gt'" := by native_decide
private theorem gt'_output : (eitherFactory["gt'"]'gt'_mem).output = .tcons "bool" [] := by native_decide
private theorem gt'_inputTys : (eitherFactory["gt'"]'gt'_mem).inputs.values =
    [.tcons "int" [], .tcons "int" []] := by native_decide
private theorem gt'_inputKeyNames :
    (eitherFactory["gt'"]'gt'_mem).inputs.map (·.1.name) = ["x", "y"] := by native_decide

-- Body comparison needs BEq workaround for Identifier Unit (_redArg linking issue)
section BEqIdent

@[local instance] private def beqIdentifierUnit : BEq (Identifier Unit) where
  beq a b := a.name == b.name

private theorem beqIdentifierUnit_sound (a b : Identifier Unit) :
    (a == b) = true → a = b := by
  simp [beqIdentifierUnit]
  intro h
  cases a; cases b; simp at h; simp [h]

private theorem gt'_body_beq : ((eitherFactory["gt'"]'gt'_mem).body == gt'Func.body) = true := by native_decide

private theorem beqIdent_eq_decEq (a b : Identifier Unit) :
    @BEq.beq _ beqIdentifierUnit a b = @BEq.beq _ instBEqOfDecidableEq a b := by
  simp only [BEq.beq]
  cases a; cases b; simp

private theorem beqExpr_eq_ident {T: LExprParamsT} [BEq T.base.Metadata] [BEq T.TypeType]
    (H1 H2: BEq (Identifier T.base.IDMeta))
    (Heq: ∀ a b, H1.beq a b = H2.beq a b) (e1 e2: LExpr T) :
    @LExpr.beq T _ _ H1 e1 e2 = @LExpr.beq T _ _ H2 e1 e2 := by
  induction e1 generalizing e2 with
  | const _ _ => cases e2 <;> simp [LExpr.beq]
  | op _ o1 _ => cases e2 <;> simp [LExpr.beq]; rename_i _ o2 _; rw [Heq o1 o2]
  | bvar _ _ => cases e2 <;> simp [LExpr.beq]
  | fvar _ n1 _ => cases e2 <;> simp [LExpr.beq]; rename_i _ n2 _; rw [Heq n1 n2]
  | abs _ _ _ _ ih => cases e2 <;> simp [LExpr.beq]; rw [ih]
  | quant _ _ _ _ _ _ ih_tr ih_e => cases e2 <;> simp [LExpr.beq]; rw [ih_tr, ih_e]
  | app _ _ _ ih_fn ih_e => cases e2 <;> simp [LExpr.beq]; rw [ih_fn, ih_e]
  | ite _ _ _ _ ih_c ih_t ih_e => cases e2 <;> simp [LExpr.beq]; rw [ih_c, ih_t, ih_e]
  | eq _ _ _ ih_a ih_b => cases e2 <;> simp [LExpr.beq]; rw [ih_a, ih_b]

private theorem gt'_body_eq :
    (eitherFactory["gt'"]'gt'_mem).body = gt'Func.body := by
  have h := gt'_body_beq
  simp only[BEq.beq, Option.instBEq.beq] at h
  split at h <;> try contradiction
  rename_i a b ha hb
  have heq : @LExpr.beq TP.mono _ _ instBEqOfDecidableEq a b = true := by
    rw [← beqExpr_eq_ident (T := TP.mono) beqIdentifierUnit instBEqOfDecidableEq
          (fun a b => beqIdent_eq_decEq a b)]
    exact h
  rw [LExpr.beq_eq (T := TP.mono)] at heq
  rw [ha, hb, heq]

end BEqIdent

-- Int.Gt field lemmas
private theorem intGt_name : (eitherFactory["Int.Gt"]'intGt_mem).name.name = "Int.Gt" := by native_decide
private theorem intGt_inputTys : (eitherFactory["Int.Gt"]'intGt_mem).inputs.values =
    [.tcons "int" [], .tcons "int" []] := by native_decide
private theorem intGt_output : (eitherFactory["Int.Gt"]'intGt_mem).output = .tcons "bool" [] := by native_decide

-- Either$Elim field lemmas
private theorem elim_name : (eitherFactory["Either$Elim"]'elim_mem).name.name = "Either$Elim" := by native_decide
private theorem elim_output : (eitherFactory["Either$Elim"]'elim_mem).output = .ftvar "$__ty0" := by native_decide
private theorem elim_inputTys : (eitherFactory["Either$Elim"]'elim_mem).inputs.values =
    [.tcons "Either" [.ftvar "a", .ftvar "b"],
     .arrow (.ftvar "a") (.ftvar "$__ty0"),
     .arrow (.ftvar "b") (.ftvar "$__ty0")] := by native_decide

private theorem elim_proof_irrel (h : "Either$Elim" ∈ eitherFactory) :
    eitherFactory["Either$Elim"]'h = eitherFactory["Either$Elim"]'elim_mem := by rfl

/-- The concreteEval stored at "Either$Elim" is `elimConcreteEval eitherBlock default`.
Blocked by `mkIdx` being `@[irreducible]`. -/
private theorem elim_ceval_eq (ceval : TP.Metadata → List (LExpr TP.mono) → Option (LExpr TP.mono))
    (h : (eitherFactory["Either$Elim"]'elim_mem).concreteEval = some ceval) :
    ceval = elimConcreteEval (T := TP) eitherBlock default := by
  sorry

private theorem intGt_proof_irrel (h : "Int.Gt" ∈ eitherFactory) :
    eitherFactory["Int.Gt"]'h = eitherFactory["Int.Gt"]'intGt_mem := by rfl

/-- The concreteEval stored at "Int.Gt" in the factory is the binaryOp eval
for `(· > ·)`. This is blocked by `mkIdx` being `@[irreducible]` — HashMap
lookups don't reduce in the kernel. -/
private theorem intGt_ceval_eq (ceval : TP.Metadata → List (LExpr TP.mono) → Option (LExpr TP.mono))
    (h : (eitherFactory["Int.Gt"]'intGt_mem).concreteEval = some ceval) :
    ∀ md (e1 e2 : LExpr TP.mono),
    ceval md [e1, e2] = match LExpr.denoteInt e1, LExpr.denoteInt e2 with
      | some a, some b => some (.boolConst md (a > b))
      | _, _ => none := by
  sorry

private theorem eitherInterpConsistent :
    Factory.InterpConsistent eitherTcInterp eitherOpInterp eitherFactory := by
  constructor
  · -- body consistency
    intro f hf body hbody
    have hmem := eitherFactory_mem f hf
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · simp [elim_no_body] at hbody    -- Either$Elim: no body
    · simp [left_no_body] at hbody    -- Left: no body
    · simp [right_no_body] at hbody   -- Right: no body
    · simp [intGt_no_body] at hbody   -- Int.Gt: no body
    · -- gt': has body
      unfold LFunc.InterpConsistentBody
      rw [gt'_name, gt'_output]
      have hbe := gt'_body_eq
      rw [hbody] at hbe
      have hbody_eq : body = (gt'Func).body.get (by simp [gt'Func]) := by
        cases hbe; rfl
      subst hbody_eq
      intro vt fvarVal
      match hinp : (eitherFactory["gt'"]'gt'_mem).inputs with
      | [(id_x, ty_x), (id_y, ty_y)] =>
        have htx : ty_x = .tcons "int" [] := by
          have := gt'_inputTys; simp [ListMap.values, hinp] at this; exact this.1
        have hty : ty_y = .tcons "int" [] := by
          have := gt'_inputTys; simp [ListMap.values, hinp] at this; exact this.2
        subst htx; subst hty
        -- Reduce substTyVars BEFORE introducing args so types are concrete
        simp only [List.map, LMonoTy.substTyVars, LMonoTy.substTyVars.map,
                   LSort.mkArrow, eitherOpInterp]
        -- Determine id_x and id_y from factory
        have hnames := gt'_inputKeyNames
        rw [hinp] at hnames; simp at hnames
        have hid_x : id_x = ⟨"x", ()⟩ := by cases id_x; simp at hnames; simp [hnames.1]
        have hid_y : id_y = ⟨"y", ()⟩ := by cases id_y; simp at hnames; simp [hnames.2]
        subst hid_x; subst hid_y
        intro h_body args
        match args with
        | .cons val_x (.cons val_y .nil) =>
          -- Unfold body
          simp only [gt'Func] at h_body ⊢
          simp only [Option.get] at h_body ⊢
          -- Peel apps
          have ⟨t1, ht1_fn, ht1_arg⟩ := HasTypeA.app_inv h_body
          rw [denote_app .nil ht1_fn ht1_arg]
          have ⟨t2, ht2_fn, ht2_arg⟩ := HasTypeA.app_inv ht1_fn
          rw [denote_app .nil ht2_fn ht2_arg]
          rw [denote_op, denote_fvar, denote_fvar]
          simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map, eitherOpInterp]
          have ht1_eq : t1 = .tcons "int" [] := HasTypeA.fvar_inv ht1_arg
          have ht2_eq : t2 = .tcons "int" [] := HasTypeA.fvar_inv ht2_arg
          subst ht1_eq; subst ht2_eq
          -- LHS: unfold applyArgs to get intGtInterp val_x val_y
          unfold SortDenote.applyArgs
          simp only []
          unfold SortDenote.applyArgs
          simp only []
          -- RHS: unfold withArgs and simplify if-then-else
          unfold IdentInterp.withArgs
          simp only []
          -- if True → first branch, dite True → val_x for first arg
          simp only [ite_true, dite_true]
          -- if ⟨"y",()⟩ = ⟨"x",()⟩ → false, so else branch
          have hne : (⟨"y", ()⟩ : Identifier Unit) ≠ ⟨"x", ()⟩ := by grind
          simp only [hne, ite_false]
          -- Now need to unfold withArgs again for "y" lookup
          unfold IdentInterp.withArgs
          simp only []
          -- Simplify remaining if True / dite True and applyArgs nil
          simp only [ite_true, dite_true]
          unfold SortDenote.applyArgs
          simp only []
      | [] => have := gt'_inputTys; simp [ListMap.values, hinp] at this
      | [_] => have := gt'_inputTys; simp [ListMap.values, hinp] at this
      | _ :: _ :: _ :: _ => have := gt'_inputTys; simp [ListMap.values, hinp] at this
  · -- eval consistency
    intro f hf ceval hceval
    have hmem := eitherFactory_mem f hf
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · -- Either$Elim: has concreteEval
      unfold LFunc.InterpConsistentEval
      rw [elim_proof_irrel]
      intro vt fvarVal md tySubst argExprs resultExpr heval
      rw [show List.map Prod.snd (eitherFactory["Either$Elim"]'elim_mem).inputs
            = (eitherFactory["Either$Elim"]'elim_mem).inputs.values from
            (ListMap.values_eq_map_snd _).symm]
      rw [elim_inputTys, elim_output, elim_name]
      simp only [List.map]
      intro h_args h_result
      -- Decompose h_args: argExprs = [ex, ef, eg]
      cases h_args with
      | cons hx h_rest =>
        rename_i ex efg_list
        cases h_rest with
        | cons hf_case h_rest2 =>
          rename_i ef eg_list
          cases h_rest2 with
          | cons hg_case h_nil =>
            rename_i eg rest
            cases h_nil
            simp only [LSort.mkArrow]
            -- Unfold denoteArgs (3 steps for 3 args) and applyArgs (4 steps)
            unfold denoteArgs
            unfold denoteArgs
            unfold denoteArgs
            unfold SortDenote.applyArgs
            unfold SortDenote.applyArgs
            unfold SortDenote.applyArgs
            unfold SortDenote.applyArgs
            simp only []
            -- The denoteArgs on [] gives HList.nil, so the match reduces
            unfold denoteArgs
            simp only [eitherOpInterp]
            trace_state
            -- Normalize to explicit names
            change LExpr.denote eitherTcInterp eitherOpInterp fvarVal vt HList.nil resultExpr
              (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0")) h_result =
              eitherOpInterp "Either$Elim"
                (LSort.tcons "arrow"
                  [LMonoTy.substTyVars vt
                      (LMonoTy.subst tySubst (LMonoTy.tcons "Either" [LMonoTy.ftvar "a", LMonoTy.ftvar "b"])),
                    LSort.tcons "arrow"
                      [LMonoTy.substTyVars vt
                          (LMonoTy.subst tySubst ((LMonoTy.ftvar "a").arrow (LMonoTy.ftvar "$__ty0"))),
                        LSort.tcons "arrow"
                          [LMonoTy.substTyVars vt
                              (LMonoTy.subst tySubst ((LMonoTy.ftvar "b").arrow (LMonoTy.ftvar "$__ty0"))),
                            LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))]]])
                (LExpr.denote eitherTcInterp eitherOpInterp fvarVal vt HList.nil ex
                  (LMonoTy.subst tySubst (LMonoTy.tcons "Either" [LMonoTy.ftvar "a", LMonoTy.ftvar "b"])) hx)
                (LExpr.denote eitherTcInterp eitherOpInterp fvarVal vt HList.nil ef
                  (LMonoTy.subst tySubst ((LMonoTy.ftvar "a").arrow (LMonoTy.ftvar "$__ty0"))) hf_case)
                (LExpr.denote eitherTcInterp eitherOpInterp fvarVal vt HList.nil eg
                  (LMonoTy.subst tySubst ((LMonoTy.ftvar "b").arrow (LMonoTy.ftvar "$__ty0"))) hg_case)
            -- Bind denote results with explicit SortDenote types to expose substTyVars
            let d_result : SortDenote eitherTcInterp
                  (LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))) :=
              LExpr.denote eitherTcInterp eitherOpInterp fvarVal vt HList.nil resultExpr
                (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0")) h_result
            let d_ex : SortDenote eitherTcInterp
                  (LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.tcons "Either" [LMonoTy.ftvar "a", LMonoTy.ftvar "b"]))) :=
              LExpr.denote eitherTcInterp eitherOpInterp fvarVal vt HList.nil ex
                (LMonoTy.subst tySubst (LMonoTy.tcons "Either" [LMonoTy.ftvar "a", LMonoTy.ftvar "b"])) hx
            let d_ef : SortDenote eitherTcInterp
                  (LMonoTy.substTyVars vt (LMonoTy.subst tySubst ((LMonoTy.ftvar "a").arrow (LMonoTy.ftvar "$__ty0")))) :=
              LExpr.denote eitherTcInterp eitherOpInterp fvarVal vt HList.nil ef
                (LMonoTy.subst tySubst ((LMonoTy.ftvar "a").arrow (LMonoTy.ftvar "$__ty0"))) hf_case
            let d_eg : SortDenote eitherTcInterp
                  (LMonoTy.substTyVars vt (LMonoTy.subst tySubst ((LMonoTy.ftvar "b").arrow (LMonoTy.ftvar "$__ty0")))) :=
              LExpr.denote eitherTcInterp eitherOpInterp fvarVal vt HList.nil eg
                (LMonoTy.subst tySubst ((LMonoTy.ftvar "b").arrow (LMonoTy.ftvar "$__ty0"))) hg_case
            -- Prove sort equality: current sort = simplified sort where match can fire
            -- substTyVars and subst distribute over tcons/arrow
            have h_sort_eq :
              LSort.tcons "arrow"
                [LMonoTy.substTyVars vt
                    (LMonoTy.subst tySubst (LMonoTy.tcons "Either" [LMonoTy.ftvar "a", LMonoTy.ftvar "b"])),
                  LSort.tcons "arrow"
                    [LMonoTy.substTyVars vt
                        (LMonoTy.subst tySubst ((LMonoTy.ftvar "a").arrow (LMonoTy.ftvar "$__ty0"))),
                      LSort.tcons "arrow"
                        [LMonoTy.substTyVars vt
                            (LMonoTy.subst tySubst ((LMonoTy.ftvar "b").arrow (LMonoTy.ftvar "$__ty0"))),
                          LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))]]]
              = LSort.tcons "arrow"
                [LSort.tcons "Either"
                    [LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "a")),
                     LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "b"))],
                  LSort.tcons "arrow"
                    [LSort.tcons "arrow"
                        [LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "a")),
                         LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))],
                      LSort.tcons "arrow"
                        [LSort.tcons "arrow"
                            [LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "b")),
                             LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))],
                          LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))]]] := by
              simp only [LMonoTy.subst_tcons_pair, LMonoTy.arrow, LMonoTy.substTyVars, LMonoTy.substTyVars.map]
            -- Use h_sort_eq to cast: eitherOpInterp sort₁ = (h ▸ eitherOpInterp sort₂)
            have h_cast : eitherOpInterp "Either$Elim"
                (LSort.tcons "arrow"
                  [LMonoTy.substTyVars vt
                      (LMonoTy.subst tySubst (LMonoTy.tcons "Either" [LMonoTy.ftvar "a", LMonoTy.ftvar "b"])),
                    LSort.tcons "arrow"
                      [LMonoTy.substTyVars vt
                          (LMonoTy.subst tySubst ((LMonoTy.ftvar "a").arrow (LMonoTy.ftvar "$__ty0"))),
                        LSort.tcons "arrow"
                          [LMonoTy.substTyVars vt
                              (LMonoTy.subst tySubst ((LMonoTy.ftvar "b").arrow (LMonoTy.ftvar "$__ty0"))),
                            LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))]]])
              = h_sort_eq ▸ eitherOpInterp "Either$Elim"
                (LSort.tcons "arrow"
                  [LSort.tcons "Either"
                      [LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "a")),
                       LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "b"))],
                    LSort.tcons "arrow"
                      [LSort.tcons "arrow"
                          [LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "a")),
                           LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))],
                        LSort.tcons "arrow"
                          [LSort.tcons "arrow"
                              [LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "b")),
                               LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))],
                            LMonoTy.substTyVars vt (LMonoTy.subst tySubst (LMonoTy.ftvar "$__ty0"))]]]) := by grind
            rw [h_cast]
            simp only [eitherOpInterp, dite_true]
            -- Use sorry'd ceval lemma to extract what ceval does
            rw [elim_proof_irrel] at hceval
            have hce := elim_ceval_eq ceval hceval
            rw [hce] at heval
            sorry
    · -- Left: no concreteEval
      have := left_no_ceval; simp [Option.isNone_iff_eq_none] at this; simp [this] at hceval
    · have := right_no_ceval; simp [Option.isNone_iff_eq_none] at this; simp [this] at hceval
    · -- Int.Gt: has concreteEval
      unfold LFunc.InterpConsistentEval
      rw [intGt_proof_irrel]
      intro vt fvarVal md tySubst argExprs resultExpr heval
      rw [show List.map Prod.snd (eitherFactory["Int.Gt"]'intGt_mem).inputs
            = (eitherFactory["Int.Gt"]'intGt_mem).inputs.values from
            (ListMap.values_eq_map_snd _).symm]
      rw [intGt_inputTys, intGt_output, intGt_name]
      have hint : LMonoTy.subst tySubst (.tcons "int" []) = .tcons "int" [] := by
        rw [LMonoTy.subst_tcons, LMonoTys.subst_nil]
      have hbool : LMonoTy.subst tySubst (.tcons "bool" []) = .tcons "bool" [] := by
        rw [LMonoTy.subst_tcons, LMonoTys.subst_nil]
      simp only [List.map]
      rw [hint, hbool]
      simp only [LMonoTy.substTyVars, LMonoTy.substTyVars.map]
      intro h_args h_result
      simp only [LSort.mkArrow, eitherOpInterp]
      -- Decompose h_args: argExprs = [e1, e2]
      cases h_args with
      | cons h1 h_rest =>
        rename_i e1 e2_list
        cases h_rest with
        | cons h2 h_nil =>
          rename_i e2 rest
          cases h_nil
          -- Unfold RHS: denoteArgs and applyArgs
          unfold denoteArgs
          unfold denoteArgs
          unfold SortDenote.applyArgs
          unfold SortDenote.applyArgs
          unfold SortDenote.applyArgs
          simp only []
          unfold denoteArgs
          simp only []
          -- Use sorry'd ceval lemma to extract what ceval does
          rw [intGt_proof_irrel] at hceval
          have hce := intGt_ceval_eq ceval hceval
          rw [hce] at heval
          -- Now heval : match denoteInt e1, denoteInt e2 with ... = some resultExpr
          -- Case split on denoteInt results
          match hd1 : LExpr.denoteInt e1, hd2 : LExpr.denoteInt e2 with
          | some a, some b =>
            simp only [hd1, hd2] at heval
            cases heval
            -- Extract e1 = intConst from hd1
            cases e1 with
            | const m1 c1 =>
              cases c1 with
              | intConst i1 =>
                simp [LExpr.denoteInt] at hd1; subst hd1
                -- Extract e2 = intConst from hd2
                cases e2 with
                | const m2 c2 =>
                  cases c2 with
                  | intConst i2 =>
                    simp [LExpr.denoteInt] at hd2; subst hd2
                    -- Now goal is fully concrete
                    unfold LExpr.boolConst
                    rw [denote_boolConst, denote_intConst, denote_intConst]
                    simp [intGtInterp]
                  | _ => simp [LExpr.denoteInt] at hd2
                | _ => simp [LExpr.denoteInt] at hd2
              | _ => simp [LExpr.denoteInt] at hd1
            | _ => simp [LExpr.denoteInt] at hd1
          | some _, none => simp only [hd1, hd2] at heval; cases heval
          | none, _ => simp only [hd1] at heval; cases heval
    · -- gt': no concreteEval
      have := gt'_no_ceval; simp [Option.isNone_iff_eq_none] at this; simp [this] at hceval

-- Factory.get is proof-irrelevant: result doesn't depend on the membership proof
private theorem left_proof_irrel (h : "Left" ∈ eitherFactory) :
    eitherFactory["Left"]'h = eitherFactory["Left"]'left_mem := by rfl

private theorem right_proof_irrel (h : "Right" ∈ eitherFactory) :
    eitherFactory["Right"]'h = eitherFactory["Right"]'right_mem := by rfl


-- Left/Right inputs and output
private theorem left_inputTys : (eitherFactory["Left"]'left_mem).inputs.values = [.ftvar "a"] := by native_decide
private theorem left_output : (eitherFactory["Left"]'left_mem).output = .tcons "Either" [.ftvar "a", .ftvar "b"] := by native_decide
private theorem left_name : (eitherFactory["Left"]'left_mem).name.name = "Left" := by native_decide
private theorem right_inputTys : (eitherFactory["Right"]'right_mem).inputs.values = [.ftvar "b"] := by native_decide
private theorem right_output : (eitherFactory["Right"]'right_mem).output = .tcons "Either" [.ftvar "a", .ftvar "b"] := by native_decide
private theorem right_name : (eitherFactory["Right"]'right_mem).name.name = "Right" := by native_decide

-- isConstr facts
private theorem left_isConstr : (eitherFactory["Left"]'left_mem).isConstr = true := by native_decide
private theorem right_isConstr : (eitherFactory["Right"]'right_mem).isConstr = true := by native_decide
private theorem elim_not_constr : (eitherFactory["Either$Elim"]'elim_mem).isConstr = false := by native_decide
private theorem intGt_not_constr : (eitherFactory["Int.Gt"]'intGt_mem).isConstr = false := by native_decide
private theorem gt'_not_constr : (eitherFactory["gt'"]'gt'_mem).isConstr = false := by native_decide

-- Helper: constructors in the factory are exactly Left and Right (by name)
private theorem eitherFactory_constr_names :
    (eitherFactory.toArray.toList.filter (·.isConstr)).map (·.name.name) = ["Left", "Right"] := by
  native_decide

private theorem eitherFactory_constr_is_left_or_right (f : LFunc TP)
    (hf : f ∈ eitherFactory.toArray) (hc : f.isConstr = true) :
    f.name.name = "Left" ∨ f.name.name = "Right" := by
  have hfilter : f ∈ eitherFactory.toArray.toList.filter (·.isConstr) := by
    rw [List.mem_filter]
    grind
  have hmap : f.name.name ∈ (eitherFactory.toArray.toList.filter (·.isConstr)).map (·.name.name) := by grind
  rw [eitherFactory_constr_names] at hmap
  simp at hmap
  exact hmap

-- Helper: disjointness when n1 is Left and n2 is Right
private theorem either_constr_disjoint_left_right
    (f1 f2 : LFunc TP)
    (f1_in : f1 ∈ eitherFactory.toArray) (f2_in : f2 ∈ eitherFactory.toArray)
    (h1 : f1.name.name = "Left") (h2 : f2.name.name = "Right")
    (vt : TyVarVal) :
    let inputSorts1 := f1.inputs.values.map (LMonoTy.substTyVars vt)
    let inputSorts2 := f2.inputs.values.map (LMonoTy.substTyVars vt)
    let outputSort1 := LMonoTy.substTyVars vt f1.output
    let outputSort2 := LMonoTy.substTyVars vt f2.output
    let fullSort1 := LSort.mkArrow outputSort1 inputSorts1
    let fullSort2 := LSort.mkArrow outputSort2 inputSorts2
    ∀ (heq : outputSort1 = outputSort2)
      (args1 : HList (SortDenote eitherTcInterp) inputSorts1)
      (args2 : HList (SortDenote eitherTcInterp) inputSorts2),
      heq ▸ SortDenote.applyArgs eitherTcInterp (eitherOpInterp f1.name.name fullSort1) args1 ≠
      SortDenote.applyArgs eitherTcInterp (eitherOpInterp f2.name.name fullSort2) args2 := by
  have ⟨_, hf1_eq⟩ := Factory.mem_name_eq_getElem f1_in h1
  have ⟨_, hf2_eq⟩ := Factory.mem_name_eq_getElem f2_in h2
  subst hf1_eq; subst hf2_eq
  rw [left_name, right_name, left_inputTys, right_inputTys, left_output, right_output]
  simp only [List.map, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LSort.mkArrow]
  intro _ args1 args2
  simp only [eitherOpInterp, dite_true]
  match args1, args2 with
  | .cons val1 .nil, .cons val2 .nil =>
    unfold SortDenote.applyArgs
    simp only []
    unfold Lambda.SortDenote.applyArgs
    intro C
    contradiction

private theorem eitherConstrConsistent :
    ConstrInterpConsistent eitherTcInterp eitherOpInterp eitherFactory := by
  constructor
  · -- constr_disjoint
    intros f1 f2 f1_in f2_in f1_constr f2_constr f_names vt inputSorts inputSorts2 outputSort1 outputSort2 fullSort1 fullSort2 heq args1 args2
    have hf1 := eitherFactory_constr_is_left_or_right f1 f1_in f1_constr
    have hf2 := eitherFactory_constr_is_left_or_right f2 f2_in f2_constr
    -- Use mem_name_eq_getElem to get f1/f2 as concrete factory elements
    rcases hf1 with h1 | h1 <;> rcases hf2 with h2 | h2
    · exact absurd (h1.trans h2.symm) f_names
    · exact either_constr_disjoint_left_right f1 f2 f1_in f2_in h1 h2 vt heq args1 args2
    · -- Right/Left: use helper with swapped args, then Ne.symm
      have hlr := either_constr_disjoint_left_right f2 f1 f2_in f1_in h2 h1 vt heq.symm args2 args1
      grind
    · exact absurd (h1.trans h2.symm) f_names
  · -- constr_injective
    intro f hf hc vt
    have hnames := eitherFactory_constr_is_left_or_right f hf hc
    rcases hnames with hname | hname
    · -- Left
      have ⟨_, hf_eq⟩ := Factory.mem_name_eq_getElem hf hname
      subst hf_eq
      rw [left_name, left_inputTys, left_output]
      simp only [List.map, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LSort.mkArrow]
      intro args1 args2
      simp only [eitherOpInterp, dite_true]
      match args1, args2 with
      | .cons val1 .nil, .cons val2 .nil =>
        unfold SortDenote.applyArgs
        simp only []
        unfold Lambda.SortDenote.applyArgs
        intros C; unfold leftInterp at C
        simp at C
        grind
    · -- Right
      have ⟨_, hf_eq⟩ := Factory.mem_name_eq_getElem hf hname
      subst hf_eq
      rw [right_name, right_inputTys, right_output]
      simp only [List.map, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LSort.mkArrow]
      intro args1 args2
      simp only [eitherOpInterp, dite_true]
      match args1, args2 with
      | .cons val1 .nil, .cons val2 .nil =>
        unfold SortDenote.applyArgs
        simp only []
        unfold Lambda.SortDenote.applyArgs
        intros C; unfold rightInterp at C
        simp at C
        grind

/-! ### Full interpretation -/

private noncomputable def eitherInterp : Interp eitherFactory where
  tcInterp := eitherTcInterp
  opInterp := eitherOpInterp
  allInhabited := inferInstance
  interpConsistent := eitherInterpConsistent
  constrConsistent := eitherConstrConsistent

end Lambda
