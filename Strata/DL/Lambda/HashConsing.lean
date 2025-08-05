/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Std.Data.HashMap

import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Identifiers
import Strata.DL.Lambda.MetaData

namespace Lambda
open Std (ToFormat Format format)

inductive QuantifierKind
  | all
  | exist
  deriving Repr, DecidableEq, Hashable


/--
MIDI Expressions.

We want structure-sharing for common subterms for efficiency. As such, we
distinguish between hashed and unhashed expressions. `LExprNode` signifies
unhashed expressions, and when they are hashed, they become `LExpr`. Thus, our
hash table maps `LExprNode` keys to `LExpr` values.

Note that we use the locally nameless representation for this abstract syntax
with variable bindings. See https://chargueraud.org/research/2009/ln/main.pdf

We implement maximal structure sharing using the scheme described in the
paper "Type-Safe Modular Hash-Consing"
(https://dl.acm.org/doi/10.1145/1159876.1159880).
-/

structure HashConsed (α : Type) where
  node : α
  tag : Int
  deriving Repr

inductive LExprNode (Identifier : Type) : Type where
  | const (c : String) (ty : Option LMonoTy)
  | op      (o : Identifier) (ty : Option LMonoTy)
  | bvar    (deBruijnIndex : Nat)
  | fvar    (name : Identifier) (ty : Option LMonoTy)
  | mdata   (info : Info) (e : HashConsed (LExprNode Identifier))
  | abs     (ty : Option LMonoTy) (e : HashConsed (LExprNode Identifier))
  | quant   (k : QuantifierKind) (ty : Option LMonoTy) (e : HashConsed (LExprNode Identifier))
  | app     (fn e : HashConsed (LExprNode Identifier))
  | ite     (c t e : HashConsed (LExprNode Identifier))
  | eq      (e1 e2 : HashConsed (LExprNode Identifier))
  deriving Repr

abbrev LExprH (Identifier : Type) := HashConsed (LExprNode Identifier)

instance : ToString (LExprNode String) where toString a := toString (repr a)
instance : ToString (LExprH String) where toString a := toString (repr a)

/--
Induction rule for `LExprNode`.

The `induction` tactic does not support nested or mutual inductive types; the
eliminator `LExprNode.rec` has multiple motives. So we define our own induction
principle below.
-/
@[induction_eliminator]
theorem LExprNode.induct (P : LExprNode Identifier → Prop)
  (caseConst : ∀c oty, P (.const c oty))
  (caseOp : ∀o oty, P (.op o oty))
  (caseBvar : ∀b, P (.bvar b))
  (caseFvar : ∀f oty, P (.fvar f oty))
  (caseMdata : ∀info (e : HashConsed (LExprNode Identifier)), P e.node → P (.mdata info e))
  (caseAbs : ∀oty (e : HashConsed (LExprNode Identifier)), P e.node → P (.abs oty e))
  (caseQuant : ∀k oty (e : HashConsed (LExprNode Identifier)), P e.node → P (.quant k oty e))
  (caseApp : ∀(fn e : HashConsed (LExprNode Identifier)), P fn.node → P e.node → P (.app fn e))
  (caseIte : ∀(c t e : HashConsed (LExprNode Identifier)), P c.node → P t.node → P e.node → P (.ite c t e))
  (caseEq : ∀(e1 e2 : HashConsed (LExprNode Identifier)), P e1.node → P e2.node → P (.eq e1 e2)) :
  ∀ n, P n := by
  intro n
  apply LExprNode.rec
  · exact caseConst
  · exact caseOp
  · exact caseBvar
  · exact caseFvar
  · exact caseMdata
  · exact caseAbs
  · exact caseQuant
  · exact caseApp
  · exact caseIte
  · exact caseEq
  · simp



variable [Hashable Identifier] [BEq Identifier] [LawfulBEq Identifier]

/--
Boolean equality for `LExprNode` -- we intend to mimic pointer
equality with this function.

Note that we cannot prove that this function is lawful (i.e.,
`LawfulBEq`) -- if `LExprNode.beq x y` then `x = y`. That's only
guaranteed if our tagging and caching mechanism satisfies certain
well-formedness properties.
-/
def LExprNode.beq (x y : LExprNode Identifier) : Bool :=
  match x, y with
  | .const a oty1, .const b oty2 => a == b && oty1 == oty2
  | .op a oty1, .op b oty2 => a == b && oty1 == oty2
  | .bvar a, .bvar b => a == b
  | .fvar a oty1, .fvar b oty2 => a == b && oty1 == oty2
  | .mdata info1 a, .mdata info2 b => info1 == info2 && a.tag == b.tag
  | .abs oty1 a, .abs oty2 b => oty1 == oty2 && a.tag == b.tag
  | .quant k1 oty1 a, .quant k2 oty2 b => k1 == k2 && oty1 == oty2 && a.tag == b.tag
  | .app a1 a2, .app b1 b2 => a1.tag == b1.tag && a2.tag == b2.tag
  | .ite c1 t1 f1, .ite c2 t2 f2 => c1.tag == c2.tag && t1.tag == t2.tag && f1.tag == f2.tag
  | .eq a1 a2, .eq b1 b2 => a1.tag == b1.tag && a2.tag == b2.tag
  | _, _ => false

instance : BEq (LExprNode Identifier) where
  beq := LExprNode.beq

theorem LExprNode.beq_rfl :
  ∀ {a : (LExprNode Identifier)}, (LExprNode.beq a a) = true := by
  intro a
  cases a <;> simp_all!

theorem LExprNode.beq_symm :
  ∀ {a b : LExprNode Identifier}, (LExprNode.beq a b) = true → (LExprNode.beq b a) = true := by
  intro a b; simp [LExprNode.beq]
  split <;> simp_all!
  -- intro h_eq h_ty
  -- exact BEq.symm h_eq
  -- intro h_eq h_ty
  -- exact BEq.symm h_eq

theorem LExprNode.beq_trans :
  ∀ {a b c : LExprNode Identifier}, (LExprNode.beq a b) = true →
                          (LExprNode.beq b c) = true →
                          (LExprNode.beq a c) = true := by
  intro a b c
  simp [LExprNode.beq]; split <;> simp_all
  all_goals (split <;> simp_all)
  -- intro h_eq_aa h_ty h_eq_ab h_ty2
  -- exact BEq.trans h_eq_aa h_eq_ab
  -- intro h_eq_aa h_ty h_eq_ab h_ty2
  -- exact BEq.trans h_eq_aa h_eq_ab


instance  : EquivBEq (LExprNode Identifier)  where
  rfl := LExprNode.beq_rfl
  symm := LExprNode.beq_symm
  trans := LExprNode.beq_trans

/--
Hash function for `LExprNode` that is compatible with `LExprNode.beq`.
Note: Type class instances for Hashable LMonoTy and Hashable Info are available with their definitions
-/
def LExprNode.hash' [Hashable Identifier] (n : LExprNode Identifier) : UInt64 :=
  match n with
  | .const c ty => hash (".const", c, ty)
  | .op o ty => hash (".op", o, ty)
  | .bvar b => hash (".bvar", b)
  | .fvar name ty => hash (".fvar", name, ty)
  | .mdata info e => hash (".mdata", info, e.tag)
  | .abs ty e => hash (".abs", ty, e.tag)
  | .quant k oty a => hash (k, oty, a.tag)
  | .app fn e => hash (".app", fn.tag, e.tag)
  | .ite c t f => hash (".ite", c.tag, t.tag, f.tag)
  | .eq e1 e2 => hash (".eq", e1.tag, e2.tag)

theorem LExprNode.hash'_eq :
  ∀ {a b : LExprNode Identifier}, LExprNode.beq a b → hash' a = hash' b := by
  intro a b
  simp [hash', beq]; split <;> simp_all


instance [Hashable Identifier] : Hashable (LExprNode Identifier) where
  hash := LExprNode.hash'

instance : LawfulHashable (LExprNode Identifier) where
  hash_eq a b (h : (a == b) = true) : hash a = hash b :=
    LExprNode.hash'_eq (by exact h)

def LExprH.beq (x y : LExprH Identifier) : Bool :=
  x.tag == y.tag

instance : BEq (LExprH Identifier) where
  beq := LExprH.beq

namespace LExprH



/--
A cache for Midi expressions that maps `LExprNode` keys to `LExprH` values.

`Std.HashMap` expects `LExprNode` to have compatible boolean equality
and hash functions, which is guaranteed via `EquivBEq LExprNode` and
`LawfulHashable LExprNode` instances above.
-/
structure Cache (Identifier: Type) [Hashable Identifier] [BEq Identifier] [LawfulBEq Identifier] where
  hmap  : Std.HashMap (LExprNode Identifier) (LExprH Identifier)
  count : Int := -1

def Cache.init (Identifier: Type) [Hashable Identifier] [BEq Identifier] [LawfulBEq Identifier] : (Cache Identifier) :=
  { hmap := ∅, count := -1 }

def Cache.count_ok (cache : (Cache Identifier)) : Prop :=
  -1 ≤ cache.count ∧
  (cache.count + 1).toNat = cache.hmap.size

def Cache.node_entry_ok (cache : Cache Identifier) : Prop :=
  ∀ (n1 : LExprNode Identifier),
    (match cache.hmap[n1]? with
     | some { node, tag } => node == n1 ∧ tag ≤ cache.count
     | none => True)

def Cache.tag_unique (cache : Cache Identifier) : Prop :=
  ∀ (n1 n2 : LExprNode Identifier),
    (match cache.hmap[n1]?, cache.hmap[n2]? with
      | some { node := n1', tag := tag1' },
        some { node := n2', tag := tag2' } =>
        if tag1' = tag2' then n1' == n2' else True
      | _, _ => true)

/--
A cache is well-formed if an `LExprNode` `n` maps to an `LExpr` whose
`node` field is equal to `n` and the `tag` field is less than or equal to
`cache.count`. Also, all the tags for entries in the cache are unique.

TODO: Do we need more invariants here?
-/
def Cache.WF (cache : Cache Identifier) : Prop :=
  Cache.count_ok cache ∧
  Cache.node_entry_ok cache ∧
  Cache.tag_unique cache

@[simp]
theorem Cache.init_WF :
  Cache.WF (@Cache.init Identifier _ _ _) := by
  simp [Cache.init, Cache.WF,
        Cache.count_ok, Cache.node_entry_ok, Cache.tag_unique]

def hashcons (e : LExprNode Identifier) (cache : Cache Identifier) : (LExprH Identifier) × (Cache Identifier) :=
  match cache.hmap[e]? with
  | some mexpr => (mexpr, cache)
  | none =>
    let new_cache_count := cache.count + 1
    let lexpr := { node := e, tag := new_cache_count }
    (lexpr, { cache with hmap := cache.hmap.insert e lexpr
                         count := new_cache_count } )

theorem Cache.count_ok_hashcons {n: LExprNode Identifier} {cache: Cache Identifier}  (h : Cache.WF cache) :
  let (_e, cache') := hashcons n cache
  Cache.count_ok cache' := by
  simp_all [Cache.WF]
  obtain ⟨h_count_ok, _⟩ := h
  simp [hashcons]; split <;> try simp_all
  rename_i _ h_n_not_in_map
  have h_size_insert :=
    @Std.HashMap.size_insert (LExprNode Identifier) (LExprH Identifier) _ _ cache.hmap _ _
                             n { node := n, tag := cache.count + 1 }
  simp [h_n_not_in_map] at h_size_insert
  simp_all [Cache.count_ok]
  omega

theorem Cache.node_entry_ok_hashcons {n: LExprNode Identifier} {cache: Cache Identifier} (h : Cache.WF cache) :
  let (_e, cache') := hashcons n cache
  Cache.node_entry_ok cache' := by
  simp_all [Cache.WF]
  obtain ⟨h_count_ok, h_node_entry_ok, _⟩ := h
  simp [hashcons]; split <;> try simp_all
  rename_i _ h_n_not_in_map
  simp [Cache.node_entry_ok]
  intro n1; split <;> try simp_all
  rename_i _ _ node tag heq
  have h_insert_get := @Std.HashMap.getElem?_insert (LExprNode Identifier) (LExprH Identifier) _ _ cache.hmap _ _
                        n n1 { node := n, tag := cache.count + 1 }
  split at h_insert_get <;> try simp_all
  simp [Cache.node_entry_ok] at h_node_entry_ok
  have h_node_entry_ok' := @h_node_entry_ok n1
  simp_all; omega
  done

theorem Cache.tag_unique_hashcons {n: LExprNode Identifier} {cache: Cache Identifier} (h : Cache.WF cache) :
  let (_e, cache') := hashcons n cache
  Cache.tag_unique cache' := by
  simp_all [Cache.WF]
  obtain ⟨h_count_ok, h_node_entry_ok, h_tag_unique⟩ := h
  simp [hashcons]; split <;> try simp_all
  rename_i _ h_n_not_in_map
  simp [Cache.tag_unique]
  intro n1 n2
  split <;> try simp_all
  rename_i _ _ _ n1' tag1' n2' tag2' heq1 heq2
  by_cases h_n_n1 : n == n1
  case pos => -- n == n1
    have h_insert_get_n1 := @Std.HashMap.getElem?_insert (LExprNode Identifier) (LExprH Identifier) _ _ cache.hmap _ _
                      n n1 { node := n, tag := cache.count + 1 }
    simp [h_n_n1] at h_insert_get_n1
    have h_n_n1' : n == n1' := by simp_all
    have h_tag1' : tag1' = cache.count + 1 := by simp_all
    by_cases h_n_n2 : n == n2
    case pos => -- n == n2 (and n == n1)
      have h_insert_get_n2 := @Std.HashMap.getElem?_insert (LExprNode Identifier) (LExprH Identifier) _ _ cache.hmap _ _
                  n n2 { node := n, tag := cache.count + 1 }

      have h_n1_eq_n: (n1 == n) = true := by exact LExprNode.beq_symm h_n_n1
      have h_n1_eq_n2: (n1 == n2) = true := by exact LExprNode.beq_trans h_n1_eq_n h_n_n2
      simp_all!
    case neg => -- n != n2 (and n == n1)
      have h_insert_get_n2 := @Std.HashMap.getElem?_insert (LExprNode Identifier) (LExprH Identifier) _ _ cache.hmap _ _
            n n2 { node := n, tag := cache.count + 1 }
      simp [h_n_n2] at h_insert_get_n2
      have h_cache_n2 : cache.hmap[n2]? = some { node := n2', tag := tag2' } := by simp_all
      simp [Cache.node_entry_ok] at h_node_entry_ok
      have h_node_entry_ok_n2 := @h_node_entry_ok n2
      simp_all; omega
  case neg => -- n != n1
    have h_insert_get_n1 := @Std.HashMap.getElem?_insert (LExprNode Identifier) (LExprH Identifier) _ _ cache.hmap _ _
      n n1 { node := n, tag := cache.count + 1 }
    simp [h_n_n1] at h_insert_get_n1
    have h_cache_n1 : cache.hmap[n1]? = some { node := n1', tag := tag1' } := by simp_all
    simp [Cache.node_entry_ok] at h_node_entry_ok
    have h_node_entry_ok_n1 := @h_node_entry_ok n1; simp_all
    by_cases h_n_n2 : n == n2
    case pos => -- n == n2 (and n != n1)
      have h_insert_get_n2 := @Std.HashMap.getElem?_insert (LExprNode Identifier) (LExprH Identifier) _ _ cache.hmap _ _
            n n2 { node := n, tag := cache.count + 1 }
      simp [h_n_n2] at h_insert_get_n2
      have h_n_n2' : n == n2' := by simp_all
      have h_tag2' : tag2' = cache.count + 1 := by simp_all
      simp_all; omega
    case neg => -- n != n2 (and n != n1)
      have h_insert_get_n2 := @Std.HashMap.getElem?_insert (LExprNode Identifier) (LExprH Identifier) _ _ cache.hmap _ _
                               n n2 { node := n, tag := cache.count + 1 }
      simp [h_n_n2] at h_insert_get_n2
      have h_cache_n2 : cache.hmap[n2]? = some { node := n2', tag := tag2' } := by simp_all
      simp [Cache.tag_unique] at h_tag_unique
      have h_tag_unique' := @h_tag_unique n1 n2
      simp_all
  done

/--
The `hashcons` function preserves the well-formedness of the `LExpr` cache.
-/
theorem Cache.WF_hashcons  {n: LExprNode Identifier} {cache: Cache Identifier}  (h : Cache.WF cache) :
  let (_e, cache') := hashcons n cache
  Cache.WF cache' := by
  unfold Cache.WF
  have := @Cache.node_entry_ok_hashcons
  have := @Cache.count_ok_hashcons
  have := @Cache.tag_unique_hashcons
  simp_all
  done

theorem hashcons_hashcons_lexprh {xn: LExprNode Identifier} {cache: Cache Identifier}:
  (hashcons xn cache).fst = (hashcons xn (hashcons xn cache).snd).fst := by
  simp_all [hashcons]; split <;> simp_all

theorem hashcons_hashcons_cache {xn: LExprNode Identifier} {cache: Cache Identifier} :
  (hashcons xn cache).snd = (hashcons xn (hashcons xn cache).snd).snd := by
  simp_all [hashcons]; split <;> simp_all


/-
-- TODO: Need a notion of a well-formed MExprMode w.r.t. a cache, which says that
-- all the subexpressions of LExprNode are in the cache.

theorem Cache.WF_and_beq {xn yn : LExprNode} {cache : Cache}
  (h_cache_wf : Cache.WF cache)
  (h_beq : xn == yn) :
  let (x, x_cache) := hashcons xn cache
  let (y, _) := hashcons yn x_cache
  x = y := by
  simp_all
  induction xn generalizing yn cache
  case caseConst =>
    cases yn
    case const =>
      rename_i c1 c2
      have : LExprNode.const c1 = LExprNode.const c2 := by
        unfold BEq.beq instBEqMExprNode LExprNode.beq at h_beq
        simp_all
      simp_all; subst c2
      simp_all [@hashcons_hashcons_mexpr (.const c1) cache]
    case bvar =>
      unfold BEq.beq instBEqMExprNode LExprNode.beq at h_beq
      simp_all
    repeat sorry
  case caseAbs =>
    cases yn <;> try simp_all
    case abs =>
      rename_i e1 h e2
      unfold BEq.beq instBEqMExprNode LExprNode.beq at h_beq
      simp at h_beq
      -- From `Cache.tag_unique`, we know that if `e1.tag = e2.tag`, then
      -- `e1.node == e2.node` (provided that `e1` and `e2` were previously
      -- hashconsed), which would let us use the induction hypothesis.
      sorry
    repeat sorry
  repeat sorry
  done
-/


/-
  `LExpr`s should be constructed only via these "smart
   constructors" below to ensure maximal sharing.
-/

def mkConst (c : String ) (oty: Option LMonoTy) (cache : Cache Identifier) : (LExprH Identifier) × (Cache Identifier) :=
  hashcons (.const c oty) cache

def mkOp (o: Identifier) (oty: Option LMonoTy) (cache : Cache Identifier) :=
  hashcons (.op o oty) cache

def mkBvar (index : Nat) (cache : Cache Identifier): (LExprH Identifier) × (Cache Identifier) :=
  hashcons (.bvar index) cache

def mkFvar (name : Identifier) (oty: Option LMonoTy) (cache : Cache Identifier): (LExprH Identifier) × (Cache Identifier) :=
  hashcons (.fvar name oty) cache

def mkMetaData (info: Info) (e: LExprH Identifier) (cache : Cache Identifier): (LExprH Identifier) × (Cache Identifier) :=
  hashcons (.mdata info e) cache

def mkAbs (oty: Option LMonoTy) (e : LExprH Identifier) (cache : Cache Identifier): (LExprH Identifier) × (Cache Identifier) :=
  hashcons (.abs oty e) cache

def mkQuant (k : QuantifierKind) (oty : Option LMonoTy) (e : LExprH Identifier) (cache : Cache Identifier): (LExprH Identifier) × (Cache Identifier) :=
 hashcons (.quant k oty e) cache
def mkApp (e1 e2 : LExprH Identifier) (cache : Cache Identifier): (LExprH Identifier) × (Cache Identifier) :=
  hashcons (.app e1 e2) cache

def mkIte (c t f : LExprH Identifier) (cache : Cache Identifier): (LExprH Identifier) × (Cache Identifier) :=
  hashcons (.ite c t f) cache

def mkEq (e1 e2 : LExprH Identifier) (cache : Cache Identifier): (LExprH Identifier) × (Cache Identifier) :=
  hashcons (.eq e1 e2) cache

/--
Compute the size of `e` as a tree.

Not optimized for execution efficiency; used for termination arguments.
-/
def size (e : LExprH Identifier) : Nat :=
  -- Lean can't figure out that this function terminates unless we destructure
  -- `e` using the `let` below.
  let { node := node, tag := _tag } := e
  match node with
  | .const _ _ => 1
  | .op _ _ => 1
  | .bvar _ => 1
  | .fvar _ _ => 1
  | .mdata _ e' => 1 + size e'
  | .abs _ e' => 1 + size e'
  | .quant _ _ e' => 1 + size e'
  | .app e1 e2 => 1 + size e1 + size e2
  | .ite c t f => 1 + size c + size t + size f
  | .eq e1 e2 => 1 + size e1 + size e2

/--
Tag-suppressing printing for `LExprH`.
-/
def formatLExprH (e : LExprH Identifier) [ToFormat Identifier] : Format :=
  let { node := e_node, tag := _tag } := e
  match e_node with
  | .const c oty =>
    match oty with
      | none => f!"#{c}"
      | some ty => f!"(#{c} : {ty})"
  | .op o oty =>
    match oty with
    | none => f!"~{o}"
    | some ty => f!"(~{o} : {ty})"
  | .bvar i => f!"%{i}"
  | .fvar x ty =>
    match ty with
    | none => f!"{x}"
    | some ty => f!"({x} : {ty})"
  | .mdata _info e => formatLExprH e
  | .abs _ e1 => Format.paren (f!"λ {formatLExprH e1}")
  | .quant .all _ e1 => Format.paren (f!"∀ {formatLExprH e1}")
  | .quant .exist _ e1 => Format.paren (f!"∃ {formatLExprH e1}")
  | .app e1 e2 => Format.paren (formatLExprH e1 ++ " " ++ formatLExprH e2)
  | .ite c t e => Format.paren
                      ("if " ++ formatLExprH c ++
                       " then " ++ formatLExprH t ++ " else "
                       ++ formatLExprH e)
  | .eq e1 e2 => Format.paren (formatLExprH e1 ++ " == " ++ formatLExprH e2)

def foo (cache : Cache Identifier) : (LExprH Identifier) × (LExprH Identifier) × (Cache Identifier) :=
  let (c1, cache) := (mkConst "c1" .none cache)
  let (c2, cache) := mkConst "c1" .none cache
  let (b0, cache) := mkBvar 0 cache
  let (abs0, cache) := mkAbs .none b0 cache
  -- dbg_trace s!"abs0: {abs0}"
  let (abs1, cache) := mkAbs .none b0 cache
  -- dbg_trace s!"abs1: {abs1}"
  let (app0, cache) := mkApp abs0 c1 cache
  -- dbg_trace s!"app0: {app0}"
  let (app1, cache) := mkApp abs1 c2 cache
  -- dbg_trace s!"app1: {app1}"
  (app0, app1, cache)

#eval (formatLExprH (foo (Cache.init String)).fst)
#eval formatLExprH (foo (Cache.init String)).2.1
#eval (foo (Cache.init String)).2.2.hmap.values
#eval (foo (Cache.init String)).2.2.hmap.size
#eval (foo (Cache.init String)).2.2.count

/--
Free variables in an `LExprH` are simply all the `LExprH.fvar`s in it.

Note that this function uses memoization. We map the unique tag of an `LExpr` to
the free variables found in it using a cache of type `Std.HashMap Int (List
Identifier)`.
-/
def free_vars_aux (e : LExprH Identifier) (acc : List Identifier) (map : Std.HashMap Int (List Identifier)) :
  (List Identifier) × (Std.HashMap Int (List Identifier)) :=
  let { node := node, tag := tag } := e
  match map[tag]? with
  | some _ => (acc, map)
  | none =>
    let (vars, map) :=
      match node with
      | .const _ _ => (acc, map)
      | .op _ _ => (acc, map)
      | .bvar _ => (acc, map)
      | .fvar x _ => (if x ∈ acc then acc else (x :: acc), map)
      | .abs _ e1 => free_vars_aux e1 acc map
      | .quant _ _ e => free_vars_aux e acc map
      | .app e1 e2 =>
        let (e1_vars, map) := free_vars_aux e1 acc map
        let (e2_vars, map) := free_vars_aux e2 acc map
        (e1_vars ++ e2_vars, map)
      | .ite c t f =>
        let (c_vars, map) := free_vars_aux c acc map
        let (t_vars, map) := free_vars_aux t acc map
        let (f_vars, map) := free_vars_aux f acc map
        (c_vars ++ t_vars ++ f_vars, map)
      | .eq e1 e2 =>
        let (e1_vars, map) := free_vars_aux e1 acc map
        let (e2_vars, map) := free_vars_aux e2 acc map
        (e1_vars ++ e2_vars, map)
      | .mdata m e => free_vars_aux e acc map
    let map := map.insert e.tag vars
    (vars, map)
  termination_by (size e)
  decreasing_by
    all_goals (simp_all [size]; try omega)

def free_vars (e : LExprH Identifier) : List Identifier :=
  let (vars, _) := free_vars_aux e ∅ ∅
  vars

def bar (cache : Cache String) : (LExprH String) × (Cache String) :=
  let (x, cache) := mkFvar "x" .none cache
  let (y, cache) := mkFvar "y" .none cache
  let (a0, cache) := mkAbs .none x cache
  let (a1, cache) := (mkApp a0 y) cache
  (a1, cache)

#eval formatLExprH (bar (Cache.init String)).1

#eval free_vars_aux (bar (Cache.init String)).1 ∅ ∅

#eval free_vars (bar (Cache.init String)).1

/--
Is `x` is a fresh variable w.r.t. `e`?
-/
def fresh (x : Identifier) (e : LExprH Identifier) : Bool :=
  x ∉ (free_vars e)

/-- An expression `e` is closed if has no free variables. -/
def closed (e : LExprH Identifier) : Bool :=
  free_vars e == ∅

/-- info: true -/
#guard_msgs in
#eval closed (foo (Cache.init String)).1

/-- info: false -/
#guard_msgs in
#eval closed (bar (Cache.init String)).1

@[simp]
theorem free_vars_abs {Identifier: Type} :
  free_vars { node := (.abs _ e), tag := _tag } = free_vars e := by
  simp [free_vars, free_vars_aux]

@[simp]
theorem fresh_abs :
  fresh x { node := (.abs e), tag := _tag } = fresh x e := by
  simp [fresh]

@[simp]
theorem closed_abs :
  closed { node := (.abs e), tag := _tag } = closed e := by
  simp [closed]

/--
This function replaces some bound variables in `e` by an arbitrary expression
`s` (and `s` may contain some free variables).

`subst_k k s e` keeps track of the number `k` of abstractions that have passed
by; it replaces all leaves of the form `(.bvar k)` with `s`.
-/
def subst_k (k : Nat) (s e : LExpr) (cache : Cache) : LExpr × Cache :=
  let { node := e_node, tag := _ } := e
  match e_node with
  | .const _ => (e, cache)
  | .bvar i => (if (i == k) then s else e, cache)
  | .fvar _ => (e, cache)
  | .abs e1 =>
    let (e1', cache) := subst_k (k + 1) s e1 cache
    mkAbs e1' cache
  | .app e1 e2 =>
    let (e1', cache) := subst_k k s e1 cache
    let (e2', cache) := subst_k k s e2 cache
    mkApp e1' e2' cache
  | .ite c t e =>
    let (c', cache) := subst_k k s c cache
    let (t', cache) := subst_k k s t cache
    let (e', cache) := subst_k k s e cache
    mkIte c' t' e' cache
  | .eq e1 e2 =>
    let (e1', cache) := subst_k k s e1 cache
    let (e2', cache) := subst_k k s e2 cache
    mkEq e1' e2' cache

-- mutual
-- def subst_k_node (k : Nat) (s : LExpr) (e : LExprNode) (cache : Cache) :
--   LExpr × Cache :=
--   match e with
--   | .const c => mkConst c cache
--   | .bvar i =>
--     if (i == k) then
--       (s, cache)
--     else
--        mkBvar i cache
--   | .fvar x => mkFvar x cache
--   | .abs e1 => subst_k_expr (k + 1) s e1 cache
--   | .app e1 e2 =>
--     let (e1', cache) := subst_k_expr k s e1 cache
--     let (e2', cache) := subst_k_expr k s e2 cache
--     mkApp e1' e2' cache
--   | .ite c t e =>
--     let (c', cache) := subst_k_expr k s c cache
--     let (t', cache) := subst_k_expr k s t cache
--     let (e', cache) := subst_k_expr k s e cache
--     mkIte c' t' e' cache
--   | .eq e1 e2 =>
--     let (e1', cache) := subst_k_expr k s e1 cache
--     let (e2', cache) := subst_k_expr k s e2 cache
--     mkEq e1' e2' cache
--
-- def subst_k_expr (k : Nat) (s e : LExpr) (cache : Cache) :
--     LExpr × Cache :=
--   let { node := e_node, tag := _ } := e
--   subst_k_node k s e_node cache
-- end

/--
Substitute the outermost bound variable in `e` by an arbitrary expression `s`.

This function is useful for β-reduction -- the reduction of
`app (abs e) s` can be implemented by `subst s e`. Having a locally nameless
representation allows us to avoid the pitfalls of variable shadowing and
capture. E.g., consider the following, written in the "raw" style of lambda
calculus.

`(λxλy x y) (λa b) --β--> λy (λa b) y`

If we'd used vanilla de Bruijn representation, we'd have the following instead,
where we'd need to shift the index of the free variable `b` to avoid capture:

`(λλ 1 0) (λ 5) --β--> λ (λ 6) 0`

We distinguish between free and bound variables in our notation, which allows us
to avoid such issues:

`(λλ 1 0) (λ b) --β--> (λ (λ b) 0)`
-/
def subst (s : LExpr) (e : LExpr) (cache : Cache) : LExpr × Cache :=
  subst_k 0 s e cache
  -- subst_k_expr 0 s e cache

def subst_example (cache : Cache) : LExpr × Cache :=
  let (fv, cache) := mkFvar "b" cache
  let (fn0, cache) := mkAbs fv cache
  let (b0, cache) := mkBvar 0 cache
  let (b1, cache) := mkBvar 1 cache
  let (e, cache) := mkApp b1 b0 cache
  let (fn1, cache) := mkAbs e cache
  subst fn0 fn1 cache

/--
info: { node := Midi.LExprNode.abs
            { node := Midi.LExprNode.app
                        { node := Midi.LExprNode.abs { node := Midi.LExprNode.fvar "b", tag := 0 }, tag := 1 }
                        { node := Midi.LExprNode.bvar 0, tag := 2 },
              tag := 6 },
  tag := 7 }
-/
#guard_msgs in
#eval (subst_example Cache.init).1

/-- info: 7 -/
#guard_msgs in
#eval (subst_example Cache.init).2.count

/--
This function turns some bound variables to free variables to investigate the
body of an abstraction. `var_open k x e` keeps track of the number `k` of
abstractions that have passed by; it replaces all leaves of the form `(.bvar k)`
with `(.fvar x)`.

Note that `x` is expected to be a fresh variable w.r.t. `e`.
-/
def var_open (k : Nat) (x : Identifier) (e : LExpr) (cache : Cache) : LExpr × Cache :=
  let (fvar, cache) := mkFvar x cache
  subst_k k fvar e cache

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `var_close k x e` keeps track of the number `k`
of abstractions that have passed by; it replaced all `(.fvar x)` with
`(.bvar k)`.
-/
def var_close (k : Nat) (x : Identifier) (e : LExpr) (cache : Cache) : LExpr × Cache :=
  let { node := e_node, tag := _ } := e
  match e_node with
  | .const _ => (e, cache)
  | .bvar _ => (e, cache)
  | .fvar y =>
    if (x == y) then (mkBvar k cache) else (e, cache)
  | .abs e1 =>
    let (e1', cache) := var_close (k + 1) x e1 cache
    mkAbs e1' cache
  | .app e1 e2 =>
    let (e1', cache) := var_close k x e1 cache
    let (e2', cache) := var_close k x e2 cache
    mkApp e1' e2' cache
  | .ite c t e =>
    let (c', cache) := var_close k x c cache
    let (t', cache) := var_close k x t cache
    let (e', cache) := var_close k x e cache
    mkIte c' t' e' cache
  | .eq e1 e2 =>
    let (e1', cache) := var_close k x e1 cache
    let (e2', cache) := var_close k x e2 cache
    mkEq e1' e2' cache

-- mutual
-- def var_close_node (k : Nat) (x : Identifier) (e : LExprNode) (cache : Cache) :
--     LExpr × Cache :=
--    match e with
--     | .const c => mkConst c cache
--     | .bvar b => mkBvar b cache
--     | .fvar y =>
--       if (x == y) then (mkBvar k cache) else (mkFvar y cache)
--     | .abs e1 =>
--       let (e1', cache) := var_close_expr (k + 1) x e1 cache
--       mkAbs e1' cache
--     | .app e1 e2 =>
--       let (e1', cache) := var_close_expr k x e1 cache
--       let (e2', cache) := var_close_expr k x e2 cache
--       mkApp e1' e2' cache
--     | .ite c t e =>
--       let (c', cache) := var_close_expr k x c cache
--       let (t', cache) := var_close_expr k x t cache
--       let (e', cache) := var_close_expr k x e cache
--       mkIte c' t' e' cache
--     | .eq e1 e2 =>
--       let (e1', cache) := var_close_expr k x e1 cache
--       let (e2', cache) := var_close_expr k x e2 cache
--       mkEq e1' e2' cache
--
-- def var_close_expr (k : Nat) (x : Identifier) (e : LExpr) (cache : Cache) :
--     LExpr × Cache :=
--   let { node := e_node, tag := _tag } := e
--   var_close_node k x e_node cache
-- end

def var_close_open_example (cache : Cache) : Bool :=
  let (b, cache) := mkBvar 0 cache
  let (e, cache) :=  mkAbs b cache
  let (e', cache) := var_open 0 "x" e cache
  let (e'', _cache) := var_close 0 "x" e' cache
  e' == e''

/-- info: true -/
#guard_msgs in
#eval var_close_open_example Cache.init

theorem var_close_open (h_cache_wf : Cache.WF cache) (h_fresh_x : fresh x e) :
  let (e', cache') := var_open i x e cache
  (var_close i x e' cache').1 = e := by
  cases e; rename_i node tag
  induction node generalizing i x
  case mk.caseConst c =>
    simp [var_open, var_close, LExpr.subst_k]
  case mk.caseBvar b =>
    simp [var_open, var_close, LExpr.subst_k]
    by_cases b = i <;> simp_all [var_close, mkFvar]
    sorry

  repeat sorry

end LExpr
end Midi
