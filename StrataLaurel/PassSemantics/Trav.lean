/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Entry
import StrataLaurel.Implementation.LaurelNodeKindProps

/-!
# Shape lemmas for the generic traversal

Most passes rewrite nodes with `mapStmtExprUsedM`. This file proves that this traversal
relates each input term to the output by `Shape`, with children related by `TE`, when the
input only uses supported constructs.

* `Basic e`: `e` is not a coroutine construct, returns at most
  one value, has no block invariants or block decreases clause, does not read, push or update
  the operand stack (`Stack`), and is not a `contractOf(precondition, …)`.
* `NamesOK e`: `e` does not bind or call reserved names.
* `Reserved.none`: the `Reserved` instance that reserves nothing.
* `TravR f s t`, `TE f P s t`: `t` is the traversal's result on `s`, and every subterm of
  `s` satisfies `P` (`Hered P s`).
* `trav_shape`: the traversal maps `s` to `f` applied to some `r` with `Shape (TE f P) s r`.
* `shape_refl`: a term has its own shape, with children related by `Same P`.
* `trav_notYield`, `trav_wild`, `trav_nf`, `targ_trav`: the traversal keeps the properties
  `NotYield`, `isWildcard` and "not a field access" when the node function `f` does.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

def NoStack : Variable → Prop
  | .Stack _ => False
  | .ArrayElement .. => False
  | _ => True

def Basic (e : StmtExprMd) : Prop :=
  match e.val with
  | .Yield | .Resume .. | .HasNext .. => False
  | .Var (.Stack _) => False
  | .Var (.ArrayElement ..) | .NewArray .. | .ArrayLength _ => False
  | .Assign ts v => NotYield v ∧ ∀ t ∈ ts, NoStack t.val
  | .IncrDecr _ _ t | .CompoundAssign _ t _ => NoStack t.val
  | .ContractOf ty _ => ty ≠ .Precondition
  | .Return (_ :: _ :: _) => False
  | .Block _ _ (_ :: _) _ | .Block _ _ _ (some _) => False
  | _ => True

theorem basic_ret_len {v : List StmtExprMd} {s : FileRange} (h : Basic ⟨.Return v, s⟩) : v.length ≤ 1 := by
  rcases v with _ | ⟨_, _ | ⟨_, _⟩⟩
  · simp
  · simp
  · exact (h : False).elim

section
variable [Reserved]

def VarOK : Variable → Prop
  | .Local n => ¬ Reserved.res n.text
  | .Declare p => ¬ Reserved.res p.name.text ∧ NotV p.name.text
  | .Field .. => True
  | .Stack _ => True
  | .ArrayElement .. => True

def NamesOK (e : StmtExprMd) : Prop :=
  match e.val with
  | .Var v => VarOK v
  | .Assign ts _ => ∀ t ∈ ts, VarOK t.val ∧ WOK t.val
  | .IncrDecr _ _ t => VarOK t.val ∧ WOK t.val
  | .CompoundAssign o t _ => VarOK t.val ∧ WOK t.val ∧ ¬ Reserved.resProc o.procName
  | .Try _ cs f => (∀ c ∈ cs, ¬ Reserved.res c.binding.text ∧ NotV c.binding.text) ∧ FinOK f
  | .Quantifier _ p _ _ => ¬ Reserved.res p.name.text ∧ NotV p.name.text
  | .Call none c _ _ => ¬ Reserved.resCall c
  | .Call (some _) c _ _ => ¬ Reserved.resProc c.text ∧ ¬ Reserved.resMethods
  | .Block _ l _ _ => LabOK l
  | _ => True

omit [Reserved] in
@[reducible] def Reserved.none (rl : String → Prop := fun _ => False) : Reserved where
  res := fun _ => False
  resLabel := rl
  shadow := fun _ h => h
  shadow_res := fun _ h => h
  resProc := fun _ => False
  retLabel := Option.none
  noGlobals := False
  ren := fun _ _ => False
  vret := Option.none
  vret_ok := fun _ h => (by cases h)
  vret_noret := fun _ h => (by cases h)
  ex := fun _ _ _ => False

instance {rl : String → Prop} : @TyEqC (Reserved.none rl) := @TyEqC.mk (Reserved.none rl) (fun _ _ => Iff.rfl)

omit [Reserved] in
theorem varOK_none {rl : String → Prop} (v : Variable) : @VarOK (Reserved.none rl) v := by
  cases v <;> first | exact fun h => h | trivial | exact ⟨fun h => h, @notV_none (Reserved.none rl) rfl _⟩

omit [Reserved] in
theorem wOK_none {rl : String → Prop} (v : Variable) : @WOK (Reserved.none rl) v := by
  cases v <;> first | trivial | exact @notV_none (Reserved.none rl) rfl _

omit [Reserved] in
theorem namesOK_none {rl : String → Prop} (e : StmtExprMd) : @NamesOK (Reserved.none rl) e := by
  rcases e with ⟨v, src⟩
  unfold NamesOK
  cases v
  case Call r _ _ _ => cases r <;> simp only [] <;> first | exact fun h => h | exact ⟨fun h => h, fun h => h⟩
  all_goals simp only [] <;> first
    | trivial
    | exact varOK_none _
    | exact fun t _ => ⟨varOK_none _, wOK_none _⟩
    | exact ⟨varOK_none _, wOK_none _⟩
    | exact ⟨varOK_none _, wOK_none _, fun h => h⟩
    | exact ⟨fun c _ => ⟨fun h => h, @notV_none (Reserved.none rl) rfl _⟩,
        fun x _ => @finP_none (Reserved.none rl) rfl x (fun _ _ => trivial)⟩
    | exact ⟨fun h => h, @notV_none (Reserved.none rl) rfl _⟩
    | exact fun h => h
    | exact ⟨fun h => h, fun h => h⟩
    | exact fun _ h => by cases h

variable {σ : Type}

omit [Reserved] in
theorem run_bind1 {α β : Type} (x : StateM σ α) (g : α → StateM σ β) (st : σ) :
    (x >>= g).run st = (g (x.run st).1).run (x.run st).2 := rfl

def TravR (f : Bool → StmtExprMd → StateM σ StmtExprMd) (s t : StmtExprMd) : Prop :=
  ∃ u st, ((mapStmtExprUsedM f u s).run st).1 = t

def TE (f : Bool → StmtExprMd → StateM σ StmtExprMd) (P : StmtExprMd → Prop) (s t : StmtExprMd) : Prop :=
  TravR f s t ∧ Hered P s

variable {f : Bool → StmtExprMd → StateM σ StmtExprMd}

omit [Reserved] in
theorem mapM_trav {p : StmtExprMd → Prop} (l : List {x // p x}) (g : {x // p x} → StateM σ StmtExprMd)
    (hg : ∀ x st, TravR f x.1 ((g x).run st).1) (st : σ) :
    L2 (TravR f) (l.map (·.1)) ((l.mapM g).run st).1 := by
  induction l generalizing st with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons, run_bind1, List.map_cons]
    exact .cons (hg x st) (ih _)

omit [Reserved] in
theorem mapM_rel {p : α → Prop} {R : α → β → Prop} (l : List {x // p x}) (g : {x // p x} → StateM σ β)
    (hg : ∀ x st, R x.1 ((g x).run st).1) (st : σ) :
    L2 R (l.map (·.1)) ((l.mapM g).run st).1 := by
  induction l generalizing st with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons, run_bind1, List.map_cons]
    exact .cons (hg x st) (ih _)

omit [Reserved] in
theorem mapIdxM_go_trav {p : StmtExprMd → Prop} (g : Nat → {x // p x} → StateM σ StmtExprMd)
    (hg : ∀ i x st, TravR f x.1 ((g i x).run st).1) :
    ∀ (l : List {x // p x}) (pre : List StmtExprMd) (acc : Array StmtExprMd) (st : σ),
      L2 (TravR f) pre acc.toList →
      L2 (TravR f) (pre ++ l.map (·.1)) ((List.mapIdxM.go g l acc).run st).1 := by
  intro l
  induction l with
  | nil => intro pre acc st h; simp only [List.mapIdxM.go, List.map_nil, List.append_nil]; exact h
  | cons x xs ih =>
    intro pre acc st h
    simp only [List.mapIdxM.go, run_bind1]
    have := ih (pre ++ [x.1]) (acc.push ((g acc.size x).run st).1) ((g acc.size x).run st).2
      (by simpa using h.concat (hg _ x st))
    simpa using this

omit [Reserved] in
theorem mapIdxM_trav {p : StmtExprMd → Prop} (l : List {x // p x}) (g : Nat → {x // p x} → StateM σ StmtExprMd)
    (hg : ∀ i x st, TravR f x.1 ((g i x).run st).1) (st : σ) :
    L2 (TravR f) (l.map (·.1)) ((l.mapIdxM g).run st).1 := by
  have := mapIdxM_go_trav g hg l [] #[] st .nil
  simp only [List.nil_append] at this
  exact this


omit [Reserved] in
theorem trav_kid {P : StmtExprMd → Prop} {c : StmtExprMd} (h : Hered P c) (u : Bool) (st : σ) :
    TE f P c ((mapStmtExprUsedM f u c).run st).1 :=
  ⟨⟨u, st, rfl⟩, h⟩

omit [Reserved] in
theorem L2.te {P : StmtExprMd → Prop} {l l' : List StmtExprMd} (h : L2 (TravR f) l l')
    (hk : ∀ c ∈ l, Hered P c) : L2 (TE f P) l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons ⟨hab, hk _ (List.mem_cons_self ..)⟩ (ih (fun c hc => hk c (List.mem_cons_of_mem _ hc)))

omit [Reserved] in
theorem attach_mapM_te {P : StmtExprMd → Prop} (l : List StmtExprMd) (u' : Bool) (st : σ)
    (hk : ∀ c ∈ l, Hered P c) :
    L2 (TE f P) l ((l.attach.mapM (fun (x : {x // x ∈ l}) => match x with | ⟨e, _⟩ => mapStmtExprUsedM f u' e)).run st).1 := by
  have := mapM_trav (f := f) l.attach (fun (x : {x // x ∈ l}) => match x with | ⟨e, _⟩ => mapStmtExprUsedM f u' e)
    (fun x st => (⟨u', st, rfl⟩ : TravR f x.1 _)) st
  rw [List.attach_map_subtype_val] at this
  exact this.te hk

omit [Reserved] in
theorem attach_optionMapM_te {P : StmtExprMd → Prop} (o : Option StmtExprMd) (u' : Bool) (st : σ)
    (hk : ∀ c ∈ o.toList, Hered P c) :
    ORel (TE f P) o ((o.attach.mapM (fun (x : {x // x ∈ o}) => match x with | ⟨e, _⟩ => mapStmtExprUsedM f u' e)).run st).1 := by
  cases o with
  | none => exact trivial
  | some e => exact trav_kid (hk e (by simp)) _ _

omit [Reserved] in
/-- If the node function `f` maps every term that is not a `yield` to a term that is not a `yield`,
then so does the traversal `mapStmtExprUsedM f u`. -/
theorem trav_notYield (hf : ∀ u r st, NotYield r → NotYield ((f u r).run st).1) (u : Bool)
    (s : StmtExprMd) (st : σ) (hs : NotYield s) : NotYield ((mapStmtExprUsedM f u s).run st).1 := by
  rcases s with ⟨v, src⟩
  cases v
  all_goals (rw [mapStmtExprUsedM.eq_def]; simp only [run_bind1])
  case Yield => simp [NotYield] at hs
  all_goals first
    | exact hf _ _ _ (by simp [NotYield])
    | (split <;> first
        | (exfalso; rename_i h; cases h; done)
        | exact hf _ _ _ (by simp [NotYield]))

set_option maxHeartbeats 1000000 in
/-- The traversal relates each input term to a node of the same shape. If every term satisfying `P`
is `Basic` and `NamesOK`, and `f` keeps terms that are not a `yield` free of `yield`, then for every
term `s` with `Hered P s` the traversal's result on `s` is `f` applied to some term `r` with
`Shape (TE f P) s r`: `r` has the constructor of `s`, and its children are the traversal's results
on the children of `s`. -/
theorem trav_shape {P : StmtExprMd → Prop} [TyEqC] (hP : ∀ e, P e → Basic e) (hN : ∀ e, P e → NamesOK e)
    (hf : ∀ u r st, NotYield r → NotYield ((f u r).run st).1) (u : Bool) :
    ∀ (s : StmtExprMd) (st : σ), Hered P s →
      ∃ r st1, ((mapStmtExprUsedM f u s).run st).1 = ((f u r).run st1).1 ∧ Shape (TE f P) s r := by
  have hte : TyEq := TyEqC.ok
  intro s st hs
  have hb := hP _ hs.here
  have hn := hN _ hs.here
  rcases s with ⟨v, src⟩
  have kid : ∀ c ∈ stmtExprChildren v, Hered P c := fun c hc => hs.kid hc
  cases v
  all_goals (rw [mapStmtExprUsedM.eq_def]; simp only [run_bind1])
  case IfThenElse c th el =>
    refine ⟨_, _, rfl, Shape.ite (trav_kid (kid c (by simp [stmtExprChildren])) _ _)
      (trav_kid (kid th (by simp [stmtExprChildren])) _ _) ?_⟩
    cases el with
    | none => trivial
    | some e => exact trav_kid (kid e (by simp [stmtExprChildren])) _ _
  case Block ss l invs dec =>
    rcases invs with _ | ⟨_, _⟩
    rotate_left
    · exact absurd hb (by simp [Basic])
    rcases dec with _ | _
    rotate_left
    · exact absurd hb (by simp [Basic])
    simp only [List.attach_nil, List.mapM_nil, Option.attach_none, Option.mapM_none]
    refine ⟨_, _, rfl, Shape.block (LX.ofL2 _ ?_) hn⟩
    have := mapIdxM_trav (f := f) ss.attach
      (fun i (x : {x // x ∈ ss}) => match x with | ⟨e, _⟩ => mapStmtExprUsedM f (u && i + 1 == ss.length) e)
      (fun i x st => (⟨_, st, rfl⟩ : TravR f x.1 _)) st
    rw [List.attach_map_subtype_val] at this
    exact this.te (fun c hc => kid c (by simpa [stmtExprChildren] using hc))
  case While c is d b pt =>
    refine ⟨_, _, rfl, Shape.while_ (trav_kid (kid c (by simp [stmtExprChildren])) _ _)
      (attach_mapM_te is _ _ (fun c hc => kid c (by simp only [stmtExprChildren]; simp [hc])))
      (trav_kid (kid b (by simp [stmtExprChildren])) _ _)⟩
  case Goto l d => exact ⟨_, _, rfl, Shape.jump⟩
  case Return v =>
    exact ⟨_, _, rfl, Shape.ret (basic_ret_len hb) (attach_mapM_te v _ _ (fun c hc => kid c (by simpa [stmtExprChildren] using hc)))⟩
  case LiteralInt => exact ⟨_, _, rfl, Shape.litInt⟩
  case LiteralBool => exact ⟨_, _, rfl, Shape.litBool⟩
  case LiteralString => exact ⟨_, _, rfl, Shape.litString⟩
  case LiteralDecimal => exact ⟨_, _, rfl, Shape.litDecimal⟩
  case LiteralBv => exact ⟨_, _, rfl, Shape.litBv⟩
  case Var v =>
    cases v with
    | Local n => exact ⟨_, _, rfl, Shape.var ⟨rfl, hn⟩⟩
    | Declare p => exact ⟨_, _, rfl, Shape.var ⟨rfl, ORel.tyRefl hte _, hn⟩⟩
    | Field t fn =>
      exact ⟨_, _, rfl, Shape.var ⟨trav_kid (kid t (by simp [stmtExprChildren, variableChildren])) _ _, rfl⟩⟩
    | Stack _ => exact absurd hb (by simp [Basic])
    | ArrayElement _ _ => exact absurd hb (by simp [Basic])
  case Call r fn as ta =>
    cases r with
    | none =>
      exact ⟨_, _, rfl, Shape.call (attach_mapM_te as _ _ (fun c hc => kid c (by simpa [stmtExprChildren] using hc))) (L2.tyRefl hte _) (.inl ⟨rfl, hn⟩)⟩
    | some t =>
      exact ⟨_, _, rfl, Shape.icall (trav_kid (kid t (by simp [stmtExprChildren])) _ _) rfl
        (attach_mapM_te as _ _ (fun c hc => kid c (by simp only [stmtExprChildren]; simp [hc]))) hn.1 hn.2 rfl⟩
  case New r ta => exact ⟨_, _, rfl, Shape.newRefl _ hte⟩
  case ReferenceEquals a b =>
    exact ⟨_, _, rfl, Shape.refEq (trav_kid (kid a (by simp [stmtExprChildren])) _ _)
      (trav_kid (kid b (by simp [stmtExprChildren])) _ _)⟩
  case AsType t ty => exact ⟨_, _, rfl, Shape.asType (trav_kid (kid t (by simp [stmtExprChildren])) _ _) (hte.refl _)⟩
  case IsType t ty => exact ⟨_, _, rfl, Shape.isType (trav_kid (kid t (by simp [stmtExprChildren])) _ _) (hte.refl _)⟩
  case Old v l => exact ⟨_, _, rfl, Shape.old (trav_kid (kid v (by simp [stmtExprChildren])) _ _)⟩
  case Assert c m => exact ⟨_, _, rfl, Shape.assert (trav_kid (kid c (by simp [stmtExprChildren])) _ _)⟩
  case Assume c => exact ⟨_, _, rfl, Shape.assume (trav_kid (kid c (by simp [stmtExprChildren])) _ _)⟩
  case Throw v => exact ⟨_, _, rfl, Shape.throw_ (trav_kid (kid v (by simp [stmtExprChildren])) _ _)⟩
  case Hole d ty =>
    cases ty with
    | none => exact ⟨_, _, rfl, Shape.holeNone⟩
    | some t => exact ⟨_, _, rfl, Shape.hole (hte.refl _)⟩
  case Yield => exact absurd hb (by simp [Basic])
  case Resume => exact absurd hb (by simp [Basic])
  case HasNext => exact absurd hb (by simp [Basic])
  case Assign ts v =>
    have hts := mapM_rel (R := fun (a b : VariableMd) => VarRel (TE f P) a.val b.val ∧ WOK a.val) ts.attach
      (fun ⟨v, _⟩ => do
        match (dependent := true) v with
        | ⟨.Field target fieldName, vs⟩ =>
          pure ⟨Variable.Field (← mapStmtExprUsedM f true target) fieldName, vs⟩
        | ⟨.ArrayElement a i, vs⟩ =>
          pure ⟨Variable.ArrayElement (← mapStmtExprUsedM f true a) (← mapStmtExprUsedM f true i), vs⟩
        | ⟨.Local _, _⟩ | ⟨.Declare _, _⟩ | ⟨.Stack _, _⟩ => pure v)
      (fun x st => by
        rcases x with ⟨⟨vv, vs⟩, hx⟩
        have hv : VarOK vv ∧ WOK vv := hn _ hx
        cases vv with
        | Stack _ => exact absurd (hb.2 _ hx) (by simp [NoStack])
        | ArrayElement _ _ => exact absurd (hb.2 _ hx) (by simp [NoStack])
        | Local n => exact ⟨⟨rfl, hv.1⟩, hv.2⟩
        | Declare p => exact ⟨⟨rfl, ORel.tyRefl hte _, hv.1⟩, trivial⟩
        | Field t fn =>
          exact ⟨⟨trav_kid (kid t (by
            simp only [stmtExprChildren, List.mem_append, List.mem_flatMap]
            exact Or.inl ⟨_, hx, by simp [variableChildren]⟩)) _ _, rfl⟩, trivial⟩) st
    rw [List.attach_map_subtype_val] at hts
    have hv : NotYield v := hb.1
    exact ⟨_, _, rfl, Shape.assign hts (trav_kid (kid v (by simp [stmtExprChildren])) _ _) hv
      (trav_notYield hf _ _ _ hv)⟩
  case IncrDecr md op t =>
    rcases t with ⟨tv, ts⟩
    cases tv with
    | Local n => exact ⟨_, _, rfl, Shape.incr ⟨rfl, hn.1⟩ hn.2⟩
    | Declare p => exact ⟨_, _, rfl, Shape.incr ⟨rfl, ORel.tyRefl hte _, hn.1⟩ hn.2⟩
    | Field tg fn =>
      exact ⟨_, _, rfl, Shape.incr ⟨trav_kid (kid tg (by simp [stmtExprChildren, variableChildren])) _ _, rfl⟩ hn.2⟩
    | Stack _ => exact absurd hb (by simp [Basic, NoStack])
    | ArrayElement _ _ => exact absurd hb (by simp [Basic, NoStack])
  case CompoundAssign op t r =>
    rcases t with ⟨tv, ts⟩
    cases tv with
    | Local n => exact ⟨_, _, rfl, Shape.compound ⟨rfl, hn.1⟩ hn.2.1
        (trav_kid (kid r (by simp [stmtExprChildren, variableChildren])) _ _) hn.2.2⟩
    | Declare p =>
      exact ⟨_, _, rfl, Shape.compound ⟨rfl, ORel.tyRefl hte _, hn.1⟩ hn.2.1
        (trav_kid (kid r (by simp [stmtExprChildren, variableChildren])) _ _) hn.2.2⟩
    | Field tg fn =>
      exact ⟨_, _, rfl, Shape.compound ⟨trav_kid (kid tg (by simp [stmtExprChildren, variableChildren])) _ _, rfl⟩
        hn.2.1 (trav_kid (kid r (by simp [stmtExprChildren, variableChildren])) _ _) hn.2.2⟩
    | Stack _ => exact absurd hb (by simp [Basic, NoStack])
    | ArrayElement _ _ => exact absurd hb (by simp [Basic, NoStack])
  case Quantifier md p tr b =>
    exact ⟨_, _, rfl, Shape.quant rfl (hte.refl _) hn.1 hn.2 (trav_kid (kid b (by simp [stmtExprChildren])) _ _)⟩
  case Try b cs fin =>
    have hcs := mapM_rel (R := CatchRel (TE f P)) cs.attach
      (fun (x : {x // x ∈ cs}) => match x with
        | ⟨c, _⟩ => do
          pure { c with
            predicate := (← c.predicate.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e)
            body := (← mapStmtExprUsedM f false c.body) })
      (fun x st => by
        rcases x with ⟨c, hx⟩
        have hk : ∀ e ∈ c.predicate.toList ++ [c.body], Hered P e := fun e he => kid e (by
          simp only [stmtExprChildren, List.mem_append, List.mem_flatMap]
          exact Or.inl (Or.inr ⟨c, hx, List.mem_append.mp he⟩))
        exact ⟨rfl, attach_optionMapM_te _ _ _ (fun e he => hk e (by simp [he])), trav_kid (hk _ (by simp)) _ _,
          (hn.1 c hx).1, (hn.1 c hx).2, hte.refl _⟩)
      ((mapStmtExprUsedM f false b).run st).2
    rw [List.attach_map_subtype_val] at hcs
    exact ⟨_, _, rfl, Shape.try_ (trav_kid (kid b (by simp [stmtExprChildren])) _ _) hcs
      (attach_optionMapM_te _ _ _ (fun c hc => kid c (by simp only [stmtExprChildren]; simp_all))) hn.2⟩
  case ContractOf ty fn =>
    have hu : Unsup (.ContractOf ty fn) := by simpa [Basic, Unsup] using hb
    exact ⟨_, _, rfl, Shape.unsup hu (by simpa [Unsup] using hu)⟩
  case NewArray => exact absurd hb (by simp [Basic])
  case ArrayLength => exact absurd hb (by simp [Basic])
  all_goals first
    | exact ⟨_, _, rfl, Shape.unsup trivial trivial⟩

/-- The traversal keeps the statement-position labels that are not reserved, given that the node function `f`
does and that no expansion the pass makes (`Reserved.ex`) carries one. For every term `s` with `Hered P s`, a
label `l` that is not reserved is held by the traversal's result on `s` exactly when it is held by `s`. -/
theorem trav_labels {P : StmtExprMd → Prop} [TyEqC] (hP : ∀ e, P e → Basic e) (hN : ∀ e, P e → NamesOK e)
    (hf : ∀ u r st, NotYield r → NotYield ((f u r).run st).1)
    (hfl : ∀ u r st l, ¬ Reserved.resLabel l → (l ∈ statementLabels ((f u r).run st).1 ↔ l ∈ statementLabels r))
    (hX : ∀ l, ¬ Reserved.resLabel l → ExLabFree (TE f P) l) (l : String) (hl : ¬ Reserved.resLabel l)
    (s : StmtExprMd) (u : Bool) (st : σ) (hs : Hered P s) :
    (l ∈ statementLabels ((mapStmtExprUsedM f u s).run st).1 ↔ l ∈ statementLabels s) := by
  obtain ⟨r, st1, heq, hsh⟩ := trav_shape hP hN hf u s st hs
  rw [heq]
  refine (hfl u r st1 l hl).trans ?_
  refine (Shape.labels _ (hX l hl) hsh (fun a b hab hmem => ?_)).symm
  obtain ⟨⟨u', st', rfl⟩, hha⟩ := hab
  exact (trav_labels hP hN hf hfl hX l hl a u' st' hha).symm
termination_by sizeOf s
decreasing_by exact stmtExprChildren_sizeOf_lt s a hmem

def Same (P : StmtExprMd → Prop) (a b : StmtExprMd) : Prop := a = b ∧ Hered P a

theorem constRel_same {P : StmtExprMd → Prop} {E : StmtExprMd → StmtExprMd → Prop} {c : Constant}
    (hE : ∀ e, Hered P e → E e e) (hP : ∀ e, c.initializer = some e → Hered P e)
    (hov : ∀ e, c.initializer = some e → OvOK condG e) (hvk : ∀ a b, Reserved.vok E a b) : ConstRel E c c := by
  refine ⟨?_, hov, fun _ _ _ _ => hvk _ _⟩
  cases hi : c.initializer with
  | none => trivial
  | some e => exact hE e (hP e hi)

theorem ConstsRel.same {E : StmtExprMd → StmtExprMd → Prop} {p q : LaurelProgram} (hq : q.constants = p.constants)
    (h : ∀ c ∈ p.constants, ConstRel E c c) : ConstsRel E p q := by
  refine ⟨p.constants, [], by rw [hq, List.append_nil], ?_, fun _ h => by cases h⟩
  clear hq
  generalize p.constants = l at h ⊢
  induction l with
  | nil => exact .nil
  | cons x xs ih => exact .cons ⟨rfl, h x (List.mem_cons_self ..)⟩ (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

omit [Reserved] in
theorem L2.same {P : StmtExprMd → Prop} (l : List StmtExprMd) (h : ∀ c ∈ l, Hered P c) : L2 (Same P) l l := by
  induction l with
  | nil => exact .nil
  | cons x xs ih =>
    exact .cons ⟨rfl, h x (List.mem_cons_self ..)⟩ (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

set_option maxHeartbeats 1000000 in
/-- If every term satisfying `P` is `Basic` and `NamesOK`, then every term `s` with `Hered P s` has its
own shape, with each child related to itself by `Same P`. -/
theorem shape_refl {P : StmtExprMd → Prop} [TyEqC] (hP : ∀ e, P e → Basic e) (hN : ∀ e, P e → NamesOK e)
    (s : StmtExprMd) (hs : Hered P s) : Shape (Same P) s s := by
  have hte : TyEq := TyEqC.ok
  have hb := hP _ hs.here
  have hn := hN _ hs.here
  rcases s with ⟨v, src⟩
  have kid : ∀ c ∈ stmtExprChildren v, Hered P c := fun c hc => hs.kid hc
  cases v
  case IfThenElse c th el =>
    refine Shape.ite ⟨rfl, kid c (by simp [stmtExprChildren])⟩ ⟨rfl, kid th (by simp [stmtExprChildren])⟩ ?_
    cases el with
    | none => trivial
    | some e => exact ⟨rfl, kid e (by simp [stmtExprChildren])⟩
  case Block ss l invs dec =>
    rcases invs with _ | ⟨_, _⟩
    rotate_left
    · exact absurd hb (by simp [Basic])
    rcases dec with _ | _
    rotate_left
    · exact absurd hb (by simp [Basic])
    exact Shape.block (LX.ofL2 _ (L2.same ss (fun c hc => kid c (by simpa [stmtExprChildren] using hc)))) hn
  case While c is d b pt =>
    exact Shape.while_ ⟨rfl, kid c (by simp [stmtExprChildren])⟩
      (L2.same is (fun c hc => kid c (by simp only [stmtExprChildren]; simp [hc])))
      ⟨rfl, kid b (by simp [stmtExprChildren])⟩
  case Goto l d => exact Shape.jump
  case Return v =>
    exact Shape.ret (basic_ret_len hb) (L2.same v (fun c hc => kid c (by simpa [stmtExprChildren] using hc)))
  case LiteralInt => exact Shape.litInt
  case LiteralBool => exact Shape.litBool
  case LiteralString => exact Shape.litString
  case LiteralDecimal => exact Shape.litDecimal
  case LiteralBv => exact Shape.litBv
  case Var v =>
    cases v with
    | Local n => exact Shape.var ⟨rfl, hn⟩
    | Declare p => exact Shape.var ⟨rfl, ORel.tyRefl hte _, hn⟩
    | Field t fn => exact Shape.var ⟨⟨rfl, kid t (by simp [stmtExprChildren, variableChildren])⟩, rfl⟩
    | Stack _ => exact absurd hb (by simp [Basic])
    | ArrayElement _ _ => exact absurd hb (by simp [Basic])
  case Call r fn as ta =>
    cases r with
    | none =>
      exact Shape.call (L2.same as (fun c hc => kid c (by simpa [stmtExprChildren] using hc))) (L2.tyRefl hte _) (.inl ⟨rfl, hn⟩)
    | some t =>
      exact Shape.icall ⟨rfl, kid t (by simp [stmtExprChildren])⟩ rfl
        (L2.same as (fun c hc => kid c (by simp only [stmtExprChildren]; simp [hc]))) hn.1 hn.2 rfl
  case New r ta => exact Shape.newRefl _ hte
  case ReferenceEquals a b =>
    exact Shape.refEq ⟨rfl, kid a (by simp [stmtExprChildren])⟩ ⟨rfl, kid b (by simp [stmtExprChildren])⟩
  case AsType t ty => exact Shape.asType ⟨rfl, kid t (by simp [stmtExprChildren])⟩ (hte.refl _)
  case IsType t ty => exact Shape.isType ⟨rfl, kid t (by simp [stmtExprChildren])⟩ (hte.refl _)
  case Old v l => exact Shape.old ⟨rfl, kid v (by simp [stmtExprChildren])⟩
  case Assert c m => exact Shape.assert ⟨rfl, kid c (by simp [stmtExprChildren])⟩
  case Assume c => exact Shape.assume ⟨rfl, kid c (by simp [stmtExprChildren])⟩
  case Throw v => exact Shape.throw_ ⟨rfl, kid v (by simp [stmtExprChildren])⟩
  case Hole d ty =>
    cases ty with
    | none => exact Shape.holeNone
    | some t => exact Shape.hole (hte.refl _)
  case Yield => exact absurd hb (by simp [Basic])
  case Resume => exact absurd hb (by simp [Basic])
  case HasNext => exact absurd hb (by simp [Basic])
  case Quantifier md p tr b => exact Shape.quant rfl (hte.refl _) hn.1 hn.2 ⟨rfl, kid b (by simp [stmtExprChildren])⟩
  case Assign ts v =>
    have hts : L2 (fun (a b : VariableMd) => VarRel (Same P) a.val b.val ∧ WOK a.val) ts ts := by
      have hall : ∀ t ∈ ts, VarRel (Same P) t.val t.val ∧ WOK t.val := by
        intro t ht
        rcases t with ⟨tv, vs⟩
        have hv : VarOK tv ∧ WOK tv := hn _ ht
        cases tv with
        | Stack _ => exact absurd (hb.2 _ ht) (by simp [NoStack])
        | ArrayElement _ _ => exact absurd (hb.2 _ ht) (by simp [NoStack])
        | Local n => exact ⟨⟨rfl, hv.1⟩, hv.2⟩
        | Declare p => exact ⟨⟨rfl, ORel.tyRefl hte _, hv.1⟩, trivial⟩
        | Field tg fn =>
          exact ⟨⟨⟨rfl, kid tg (by
            simp only [stmtExprChildren, List.mem_append, List.mem_flatMap]
            exact Or.inl ⟨_, ht, by simp [variableChildren]⟩)⟩, rfl⟩, trivial⟩
      clear hb hn kid hs
      induction ts with
      | nil => exact .nil
      | cons x xs ih => exact .cons (hall x (List.mem_cons_self ..)) (ih (fun y hy => hall y (List.mem_cons_of_mem _ hy)))
    have hv : NotYield v := hb.1
    exact Shape.assign hts ⟨rfl, kid v (by simp [stmtExprChildren])⟩ hv hv
  case IncrDecr md op t =>
    rcases t with ⟨tv, ts⟩
    cases tv with
    | Local n => exact Shape.incr ⟨rfl, hn.1⟩ hn.2
    | Declare p => exact Shape.incr ⟨rfl, ORel.tyRefl hte _, hn.1⟩ hn.2
    | Field tg fn => exact Shape.incr ⟨⟨rfl, kid tg (by simp [stmtExprChildren, variableChildren])⟩, rfl⟩ hn.2
    | Stack _ => exact absurd hb (by simp [Basic, NoStack])
    | ArrayElement _ _ => exact absurd hb (by simp [Basic, NoStack])
  case CompoundAssign op t r =>
    rcases t with ⟨tv, ts⟩
    have hr : Same P r r := ⟨rfl, kid r (by simp [stmtExprChildren, variableChildren])⟩
    cases tv with
    | Local n => exact Shape.compound ⟨rfl, hn.1⟩ hn.2.1 hr hn.2.2
    | Declare p => exact Shape.compound ⟨rfl, ORel.tyRefl hte _, hn.1⟩ hn.2.1 hr hn.2.2
    | Field tg fn =>
      exact Shape.compound ⟨⟨rfl, kid tg (by simp [stmtExprChildren, variableChildren])⟩, rfl⟩ hn.2.1 hr hn.2.2
    | Stack _ => exact absurd hb (by simp [Basic, NoStack])
    | ArrayElement _ _ => exact absurd hb (by simp [Basic, NoStack])
  case Try b cs fin =>
    have hcs : L2 (CatchRel (Same P)) cs cs := by
      have hall : ∀ c ∈ cs, CatchRel (Same P) c c := by
        intro c hc
        have hk : ∀ e ∈ c.predicate.toList ++ [c.body], Hered P e := fun e he => kid e (by
          simp only [stmtExprChildren, List.mem_append, List.mem_flatMap]
          exact Or.inl (Or.inr ⟨c, hc, List.mem_append.mp he⟩))
        refine ⟨rfl, ?_, ⟨rfl, hk _ (by simp)⟩, (hn.1 c hc).1, (hn.1 c hc).2, hte.refl _⟩
        cases hp : c.predicate with
        | none => trivial
        | some e => exact ⟨rfl, hk e (by simp [hp])⟩
      clear hb hn kid hs
      induction cs with
      | nil => exact .nil
      | cons x xs ih => exact .cons (hall x (List.mem_cons_self ..)) (ih (fun y hy => hall y (List.mem_cons_of_mem _ hy)))
    refine Shape.try_ ⟨rfl, kid b (by simp [stmtExprChildren])⟩ hcs ?_ hn.2
    cases fin with
    | none => trivial
    | some e => exact ⟨rfl, kid e (by simp only [stmtExprChildren]; simp)⟩
  case ContractOf ty fn => exact Shape.unsup (by simpa [Basic, Unsup] using hb) (by simpa [Basic, Unsup] using hb)
  case NewArray => exact absurd hb (by simp [Basic])
  case ArrayLength => exact absurd hb (by simp [Basic])
  all_goals exact Shape.unsup trivial trivial


omit [Reserved] in
theorem run_pureT {α : Type} (x : α) (st : σ) : (pure x : StateM σ α).run st = (x, st) := rfl

theorem shape_nonfield {E₁ : StmtExprMd → StmtExprMd → Prop} {t r : StmtExprMd} (h : Shape E₁ t r)
    (ht : ∀ o fn, t.val ≠ .Var (.Field o fn)) : ∀ o fn, r.val ≠ .Var (.Field o fn) := by
  intro o fn hr
  rcases r with ⟨rv, rs⟩
  dsimp only at hr
  subst hr
  cases h with
  | @var v v' _ _ hv =>
    cases v <;> simp only [VarRel] at hv
    exact ht _ _ rfl
  | unsup _ hu' => exact hu'.elim

omit [Reserved] in
/-- If the node function `f` keeps `isWildcard`, then so does the traversal `mapStmtExprUsedM f u`. -/
theorem trav_wild (hg : ∀ u r st, ((f u r).run st).1.isWildcard = r.isWildcard) (u : Bool) (t : StmtExprMd) (st : σ) :
    ((mapStmtExprUsedM f u t).run st).1.isWildcard = t.isWildcard := by
  rw [mapStmtExprUsedM.eq_def]
  rcases t with ⟨v, s⟩
  cases v <;> simp only [run_bind1, run_pureT, hg] <;> (try split) <;> (try simp only [run_bind1, run_pureT, hg]) <;> rfl

omit [Reserved] in
/-- If the node function `f` maps every term that is not a field access to a term that is not a field
access, then so does the traversal `mapStmtExprUsedM f u`. -/
theorem trav_nf (hgnf : ∀ u r st, (∀ o fn, r.val ≠ .Var (.Field o fn)) → ∀ o fn, ((f u r).run st).1.val ≠ .Var (.Field o fn))
    (u : Bool) (t : StmtExprMd) (ht : ∀ o fn, t.val ≠ .Var (.Field o fn)) (st : σ) :
    ∀ o fn, ((mapStmtExprUsedM f u t).run st).1.val ≠ .Var (.Field o fn) := by
  rw [mapStmtExprUsedM.eq_def]
  rcases t with ⟨v, s⟩
  cases v <;> simp only [run_bind1, run_pureT] <;> (try split) <;> (try simp only [run_bind1, run_pureT]) <;>
    first
    | exact absurd rfl (ht _ _)
    | (apply hgnf; intro o fn h; cases h; done)
    | (apply hgnf; intro o fn h; simp_all; done)
    | (simp_all; done)

/-- Each assignment target `t` with `Hered P t` is related to its traversal result by
`TargRel (TE f P)`: both are field accesses with the same field name and related receivers, or
neither is a field access and the two are related by `TE f P`. The hypotheses: `f` leaves field
accesses unchanged and does not create them, every hereditary-`P` term satisfies `OvOK condG`, and
the pass's `vok` hook holds. -/
theorem targ_trav {P : StmtExprMd → Prop}
    (hgvar : ∀ u r st, (∃ o fn, r.val = .Var (.Field o fn)) → ((f u r).run st).1 = r)
    (hgnf : ∀ u r st, (∀ o fn, r.val ≠ .Var (.Field o fn)) → ∀ o fn, ((f u r).run st).1.val ≠ .Var (.Field o fn))
    (hov : ∀ e, Hered P e → OvOK condG e) (hvk : ∀ a b, Reserved.vok (TE f P) a b)
    {t : StmtExprMd} (ht : Hered P t) (u : Bool) (st : σ) :
    TargRel (TE f P) t ((mapStmtExprUsedM f u t).run st).1 := by
  by_cases hfl : ∃ o fn, t.val = .Var (.Field o fn)
  · obtain ⟨o, fn, hv⟩ := hfl
    rcases t with ⟨tv, ts⟩
    dsimp only at hv
    subst hv
    have ho : Hered P o := ht.kid (by simp [stmtExprChildren, variableChildren])
    rw [mapStmtExprUsedM.eq_def]
    simp only [run_bind1, run_pureT]
    rw [hgvar _ _ _ ⟨_, _, rfl⟩]
    exact .inl ⟨o, fn, ts, _, fn, ts, rfl, rfl, rfl, trav_kid ho true st, hvk _ _, hov o ho⟩
  · have hfl' : ∀ o fn, t.val ≠ .Var (.Field o fn) := fun o fn h => hfl ⟨o, fn, h⟩
    exact .inr ⟨hfl', trav_nf hgnf u t hfl' st, trav_kid ht u st, hvk _ _, hov t ht⟩

theorem targRel_same {P : StmtExprMd → Prop} {E : StmtExprMd → StmtExprMd → Prop} (hE : ∀ e, Hered P e → E e e)
    (hov : ∀ e, Hered P e → OvOK condG e) (hvk : ∀ a b, Reserved.vok E a b) {t : StmtExprMd} (ht : Hered P t) :
    TargRel E t t := by
  by_cases hfl : ∃ o fn, t.val = .Var (.Field o fn)
  · obtain ⟨o, fn, hv⟩ := hfl
    rcases t with ⟨tv, ts⟩
    dsimp only at hv
    subst hv
    have ho : Hered P o := ht.kid (by simp [stmtExprChildren, variableChildren])
    exact .inl ⟨o, fn, ts, o, fn, ts, rfl, rfl, rfl, hE o ho, hvk _ _, hov o ho⟩
  · have hfl' : ∀ o fn, t.val ≠ .Var (.Field o fn) := fun o fn h => hfl ⟨o, fn, h⟩
    exact .inr ⟨hfl', hfl', hE t ht, hvk _ _, hov t ht⟩

theorem framesRel_same {P : StmtExprMd → Prop} {E : StmtExprMd → StmtExprMd → Prop} (hE : ∀ e, Hered P e → E e e)
    (hov : ∀ e, Hered P e → OvOK condG e) (hvk : ∀ a b, Reserved.vok E a b) {Pr : Procedure}
    (h : ∀ g ∈ bodyModifies Pr.body, (∀ t ∈ g.targets, Hered P t) ∧ ∀ e, g.guard = some e → Hered P e) :
    L2 (GroupRel E) (procFrames Pr) (procFrames Pr) := by
  unfold procFrames
  split
  · rename_i ms _
    have hm : ∀ g ∈ ms.filter (fun g => !hasModifiesWildcard g.targets),
        (∀ t ∈ g.targets, Hered P t) ∧ ∀ e, g.guard = some e → Hered P e := by
      intro g hg
      rename_i heq
      exact h g (by rw [heq]; exact (List.mem_filter.mp hg).1)
    generalize ms.filter (fun g => !hasModifiesWildcard g.targets) = l at hm ⊢
    induction l with
    | nil => exact .nil
    | cons g gs ih =>
      have hg := hm g (List.mem_cons_self ..)
      refine .cons ⟨?_, fun _ _ _ _ => hvk _ _, fun e he => hov e (hg.2 e he), ?_⟩
        (ih (fun x hx => hm x (List.mem_cons_of_mem _ hx)))
      · cases hgd : g.guard with
        | none => trivial
        | some e => exact hE e (hg.2 e hgd)
      · have ht := hg.1
        generalize g.targets = ts at ht ⊢
        induction ts with
        | nil => exact .nil
        | cons t ts ih2 =>
          exact .cons (targRel_same hE hov hvk (ht t (List.mem_cons_self ..)))
            (ih2 (fun x hx => ht x (List.mem_cons_of_mem _ hx)))
  · exact .nil

end

end Strata.Laurel.PassSemantics