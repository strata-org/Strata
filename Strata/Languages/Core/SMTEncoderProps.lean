/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.Languages.Core.SMTEncoder
import all Strata.DL.Lambda.TypeFactory
public import Strata.Languages.Core.SMTEncoder
public import Strata.Util.OrderedSetProps

/-!
# Coherence proofs for the SMT encoder `Context`

These proofs relate the encoder's O(1) index-based lookups to direct scans,
justifying the fast paths used during encoding.

Key results:

- `SMT.Context.committedFn_eq_any` — `committedFn`'s O(1) `ifs` key-index lookup
  agrees with a linear scan over the interpreted functions, provided the index
  is well-formed.
- `SMT.Datatypes.getType_ofFactory` — the name→datatype hash index built by
  `SMT.Datatypes.ofFactory` returns exactly what a linear scan of the underlying
  `TypeFactory` would. -/

namespace Core
open Strata.SMT
open Strata.Util

/-- `committedFn`'s O(1) index lookup agrees with a linear scan over the
    interpreted functions, provided the `ifs` index is well-formed. -/
public theorem SMT.Context.committedFn_eq_any (ctx : SMT.Context) (uf : UF)
    (h : OrderedKeyedSetWF ctx.ifs) :
    ctx.committedFn uf
      = (ctx.ufs.contains uf || ctx.ifs.toArray.any (fun f => f.toUF == uf)) := by
  simp only [SMT.Context.committedFn, h.containsKey_eq_any]

/-! ### Datatype name-index coherence

`SMT.Datatypes.ofFactory` builds the name→datatype index by folding
`Std.HashMap.insertIfNew` over the factory's datatypes. The helper below
characterizes that fold; the exported theorem then specializes it at the empty
starting map. -/

section Datatypes
open Lambda

/-- Looking up `name` after folding `insertIfNew` (keyed on `.name`) over `l`
    into a starting map `m`: `insertIfNew`'s first-wins semantics means an
    existing binding in `m` takes precedence, and otherwise the result is the
    first list element whose name matches. -/
private theorem getElem?_foldl_insertIfNew
    (l : List (LDatatype CoreLParams.IDMeta)) (name : String)
    (m : Std.HashMap String (LDatatype CoreLParams.IDMeta)) :
    (l.foldl (fun m d => m.insertIfNew d.name d) m)[name]?
      = (m[name]?).or (l.find? (·.name == name)) := by
  induction l generalizing m with
  | nil => simp only [List.foldl_nil, List.find?_nil, Option.or_none]
  | cons d l ih =>
    simp only [List.foldl_cons, List.find?_cons, ih, Std.HashMap.getElem?_insertIfNew]
    by_cases h : d.name = name
    · subst h
      simp only [beq_self_eq_true, true_and, Std.HashMap.mem_iff_isSome_getElem?, Option.or_some]
      cases m[d.name]? with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
          Option.some_or, Option.getD_none]
      | some v =>
        simp only [Option.isSome_some, not_true_eq_false, ↓reduceIte, Option.some_or,
          Option.getD_some]
    · have hne : (d.name == name) = false := beq_false_of_ne h
      simp only [hne, Bool.false_eq_true, false_and, if_false]

/-- `SMT.Datatypes.getType` agrees with `TypeFactory.getType`: the hash index
    computed by `ofFactory` returns exactly what a linear scan of the factory
    would. -/
theorem SMT.Datatypes.getType_ofFactory (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (name : String) :
    (SMT.Datatypes.ofFactory tf).getType name = tf.getType name := by
  simp only [SMT.Datatypes.getType, SMT.Datatypes.ofFactory,
    Lambda.TypeFactory.getType, Std.HashMap.get?_eq_getElem?]
  rw [getElem?_foldl_insertIfNew, Std.HashMap.getElem?_empty, Option.none_or]

end Datatypes

end Core
