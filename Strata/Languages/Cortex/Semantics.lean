/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module
public import Strata.Languages.Cortex.LowerExceptions
public import Strata.DL.Imperative.StmtSemantics

/-! # Relational semantics of Cortex

An event-trace small-step relation over Cortex configurations. It covers the base commands,
the object commands, calls and virtual calls of procedures with a body, `throw`, exception
tables and the `raised` outcome. It has no step for the array commands, nor for a call or a
virtual call of a procedure without a body.

Values are Core's semantic values (`Lambda.SemValue`) and expressions evaluate by
`Core.Expression.eval` under the factory of the environment. Evaluation types an expression by
its annotations, so an operator without a type annotation has no value, nor has any expression
that contains one. The wire format builds every operator without an annotation, and the Laurel
translation builds some without one, such as calls of functions that are not built-in
operators: the relation has no run of such a program past the first command or jump that
evaluates such an expression. Annotating the operators on the
Cortex route is a follow-up.

- **References.** A reference is a value of the datatype `Ref = Null | Obj (id : int)
  (tag : Tag)`, and `Tag` has one constant `C$Tag` per composite `C`, all distinct. Both are
  declared by the factory. The relation reads every composite type and every `$Any…` type
  as `Ref` (`eraseExpr`, `eraseCmd`), so a variable of any composite type holds any
  reference. A reference's class is its tag (`semDynType`); type tests and dispatch read
  the value, not the heap.
- **The heap** is a value of the heap API's sort `Heap`, and every heap command is the API
  operation that the factory interprets (`apiEval`): `Heap.read`, `Heap.write`,
  `Heap.allocated`, `Ref.tag`, `Heap.grows`, `Heap.onlyModifies`. Allocation (`NewObj`)
  picks any reference that the API's `Heap.new` postconditions allow. A run starts from the
  heap that the initial store binds to the reserved name `$entryHeap` (`entryHeap`), any heap
  whose allocated objects have the tag of a class (`WellTagged`).
- **Exceptions.** A command has an outcome (`COutcome`). An exception that no handler
  catches ends a procedure with `throws` in `raised`; in a procedure without `throws` it
  emits the event `CEvent.uncaught` and the procedure returns normally.
- **Constrained types.** A constrained type reads as its base type (`eraseMono`), and its
  constraint is checked where `LowerCTE` checks it: a block runs each command with the
  checks `checkedCmd` puts around it, a call assumes the constraints of the callee's inputs
  at entry (`entryChecks`), and a normal return asserts those of its outputs (`exitChecks`).
- **Calls** run the callee's body to its end (`RunBody`), copying the globals in and out,
  and emit the callee's preconditions before its body's events. The callee's entry store
  holds the arguments, values of the inputs' types, at the inputs and values of their types
  at the outputs that are not inputs (`CallFrame`); an output that is also an input holds
  the argument. A call writes each result to its target only if the result has the type of
  the value the target holds, as an assignment does (`valueOfStoredTy`). A normal return
  emits the callee's postconditions, which read the outputs and globals at return,
  the inputs that are not outputs at entry, and `old x` at entry for a global or an input
  and output `x`.

## Key definitions

- `Program.ctx`: the part of a program the relation reads.
- `eraseExpr`, `eraseCmd`, `ceval`: constrained types erased to their base types and
  reference types to `Ref`, and evaluation.
- `checkedCmd`, `entryChecks`, `exitChecks`: the checks of the constraints of constrained
  types.
- `apiEval`, `RefTagModel`, `HeapApiModel`: the heap API's operations under the factory,
  and the laws a lawful model of references and of the heap API satisfies.
- `SafeRef`, `StoreSafe`, `HeapClosed`: a reference that is `Null` or allocated, a store of
  such references, and a heap whose fields hold only such references.
- `WellTagged`, `entryHeapVar`, `entryHeap`: the invariant of a run's heaps, and the heap a
  run starts from.
- `CState`, `COutcome`, `CEvent`, `Fr`, `CConfig`: states, outcomes, events, frames and
  configurations; `semDynType`, the class of a reference.
- `NewObj`, `CallFrame`, `chosenOutputs`, `GlobalsBack`: allocation, call entry and call
  exit.
- `StepCortex`: the step relation, parametric in the command relation.
- `EvalIRCmd`, `CallProc`, `RunBody`: the mutually inductive command, call and body
  relations.
-/

namespace Cortex.Sem

open Imperative Lambda

public section

/-- A store of Core semantic values. -/
abbrev Store := SemanticStore Core.Expression

/-- A Core factory with its model. -/
abbrev Fac := Core.Expression.Factory

/-! ## Helpers on commands, calls and postconditions -/

/-- The metadata of a command. -/
@[expose] def IRCmd.md : IRCmd → MD
  | .cmd (.init _ _ _ md) | .cmd (.set _ _ md) | .cmd (.assert _ _ md) | .cmd (.assume _ _ md)
  | .cmd (.cover _ _ md) => md
  | .cast _ _ _ _ md | .new _ _ md | .readField _ _ _ md | .writeField _ _ _ md
  | .instanceOf _ _ _ md | .call _ _ _ md | .virtualCall _ _ _ _ md | .throw _ md => md
  | .newArray _ _ _ md | .readElem _ _ _ _ md | .writeElem _ _ _ _ md | .arrayLength _ _ md
  | .instanceOfComponent _ _ _ md => md

/-- The check of precondition `pre` at a call at `callMd`: located at the call, with the
precondition's property summary. -/
@[expose] def preconditionMd (callMd : MD) (pre : Precondition) : MD :=
  match pre.md.getPropertySummary with
  | some s => callMd.pushElem Imperative.MetaData.propertySummary (.msg s)
  | none => callMd

/-- The fields of an object of type `ty`: those of every composite that `ty` is a subtype of. -/
@[expose] def objectFieldRefs (prog : UnorderedProgram) (ty : LMonoTy) : List FieldRef :=
  prog.composites.flatMap fun c =>
    if prog.isSubtypeTy ty (tcon c.name) then c.fields.map fun fd => ⟨c.name, fd.name⟩ else []

/-- The entry values a postcondition reads, from the entry store `σ₀` of a procedure with
inputs `ins` and outputs `outs`: `Core.CoreIdent.mkOld x` is `x`'s entry value for every
global and every input `x` that is also an output, and an input that is not an output has
its entry value. Every other variable is undefined, so a postcondition reads it at
return. -/
@[expose] def entryOld (prog : UnorderedProgram) (ins outs : List Core.Expression.Ident)
    (σ₀ : Store) : Store :=
  fun x =>
    match (prog.globals.map Prod.fst ++ ins.filter (· ∈ outs)).find?
        (Core.CoreIdent.mkOld ·.name == x) with
    | some g => σ₀ g
    | none => if x ∈ ins ∧ x ∉ outs then σ₀ x else none

/-- The store a postcondition reads: the entry values `old`, and `σ` elsewhere. -/
@[expose] def postStore (old σ : Store) : Store := fun x => (old x).or (σ x)

/-! ## Program context -/

/-- The procedures an ordered program declares, in order. -/
@[expose] def _root_.Cortex.OrderedProgram.procedures (q : OrderedProgram) : List Procedure :=
  q.decls.filterMap fun
    | .procedure p => some p
    | _ => none

/-- The part of a program the relation reads: its composites, constrained types, globals
and procedures. An ordered program has no composites, no constrained types and no globals. -/
@[expose] def _root_.Cortex.Program.ctx : Program → UnorderedProgram
  | .unordered p =>
    { composites := p.composites, constrained := p.constrained, globals := p.globals,
      procedures := p.procedures }
  | .ordered q => { composites := [], procedures := q.procedures }

/-- A procedure of a program by name: the first one with that name. -/
@[expose] def _root_.Cortex.Program.findProcedure? (prog : Program) (n : ProcName) :
    Option Procedure :=
  prog.ctx.findProcedure? n

/-- The names of a program's globals. -/
@[expose] def globalNames (Γ : UnorderedProgram) : List Core.Expression.Ident :=
  Γ.globals.map Prod.fst

/-! ## Reference types -/

/-- The API's sort of references. -/
@[expose] def refTy : LMonoTy := .tcons "Ref" []

/-- A type name read as `Ref`: a composite of `Γ`, or a `$Any…` name. -/
@[expose] def isRefName (Γ : UnorderedProgram) (n : String) : Bool :=
  n.startsWith "$Any" || (Γ.findComposite? n).isSome

mutual
/-- `t` with every composite and `$Any…` type read as `Ref`. -/
@[expose] def eraseRefs (Γ : UnorderedProgram) : LMonoTy → LMonoTy
  | .tcons n args =>
    if args.isEmpty && isRefName Γ n then refTy else .tcons n (eraseRefsList Γ args)
  | t => t

/-- `eraseRefs` on each type of a list. -/
@[expose] def eraseRefsList (Γ : UnorderedProgram) : List LMonoTy → List LMonoTy
  | [] => []
  | t :: ts => eraseRefs Γ t :: eraseRefsList Γ ts
end

/-- The base type of the constrained type `n` among `cs`, as `Cortex.baseOf` computes it:
the base of `n`'s base when that is itself a constrained type, to a depth of `fuel`. -/
@[expose] def constrainedBase (cs : List ConstrainedDecl) (n : String) : Nat → Option LMonoTy
  | 0 => none
  | fuel + 1 =>
    match cs.find? (·.name == n) with
    | none => none
    | some c =>
      match c.base with
      | .forAll _ (.tcons b []) => (constrainedBase cs b fuel).orElse fun _ => some (.tcons b [])
      | .forAll _ t => some t

mutual
/-- The type of the values of type `t`, as `Cortex.valueTy` computes it: each constrained
type of `cs` read as its base type, except inside the element type of an array type, which
identifies the array type. -/
@[expose] def constrainedValueTy (cs : List ConstrainedDecl) : LMonoTy → LMonoTy
  | t@(.tcons n []) => (constrainedBase cs n 32).getD t
  | t@(.tcons n args) =>
    if (arrayElem? t).isSome then t else .tcons n (constrainedValueTyList cs args)
  | t => t

/-- `constrainedValueTy` on each type of a list. -/
@[expose] def constrainedValueTyList (cs : List ConstrainedDecl) : List LMonoTy → List LMonoTy
  | [] => []
  | t :: ts => constrainedValueTy cs t :: constrainedValueTyList cs ts
end

/-- `t` with every constrained type of `Γ` read as its base type, as `LowerCTE` replaces it
(`constrainedValueTy`), and then every composite and `$Any…` type read as `Ref`. -/
@[expose] def eraseMono (Γ : UnorderedProgram) (t : LMonoTy) : LMonoTy :=
  eraseRefs Γ (constrainedValueTy Γ.constrained t)

/-- `eraseMono` on a type scheme. -/
@[expose] def eraseTy (Γ : UnorderedProgram) : LTy → LTy
  | .forAll vs t => .forAll vs (eraseMono Γ t)

/-- `e` with every type annotation erased by `eraseMono`. -/
@[expose] def eraseExpr (Γ : UnorderedProgram) (e : Expr) : Expr :=
  LExpr.replaceUserProvidedType e (eraseMono Γ)

/-- A base command with its types and expressions erased. -/
@[expose] def eraseCmd (Γ : UnorderedProgram) (c : Cmd Core.Expression) : Cmd Core.Expression :=
  mapBaseCmd (eraseExpr Γ) (eraseTy Γ) c

/-- Evaluation of a Cortex expression: its erasure, evaluated by `Core.Expression.eval`. -/
@[expose] def ceval (Γ : UnorderedProgram) (f : Fac) (σ : Store) (e : Expr) : Option SemValue :=
  Core.Expression.eval f σ (eraseExpr Γ e)

/-! ## The heap API in the factory

The API's operations as annotated Core terms over the free variables `$h`, `$h'`, `$o`,
`$w`, `$t`, `$L`, `$M`, evaluated in a store that binds those variables (`apiEval`). -/

/-- The API's sort of heaps. -/
@[expose] def heapTy : LMonoTy := .tcons "Heap" []
/-- The API's sort of tags. -/
@[expose] def tagTy : LMonoTy := .tcons "Tag" []
/-- The API's sort of fields of type `t`. -/
@[expose] def fieldTy (t : LMonoTy) : LMonoTy := .tcons "Field" [t]
/-- The API's sort of field identities. -/
@[expose] def fieldIdTy : LMonoTy := .tcons "FieldId" []
/-- The API's sort of location sets. -/
@[expose] def locsTy : LMonoTy := .tcons "Locs" []

/-- The operator `n` at the monomorphic type of a function from `args` to `res`. -/
@[expose] def apiCall (n : String) (args : List LMonoTy) (res : LMonoTy) (es : List Expr) : Expr :=
  mkApp (.op Core.coreLoc ⟨n, ()⟩ (some (args.foldr LMonoTy.arrow res))) es

/-- The variable `n` of an API term. -/
@[expose] def apiVar (n : String) : Expr := mkFvar n

/-- The store binding the variables of an API term. -/
@[expose] def bindStore (bs : List (String × SemValue)) : Store := fun x => bs.lookup x.name

/-- The value of the API term `e` under `f`, its variables bound by `bs`. -/
@[expose] def apiEval (f : Fac) (bs : List (String × SemValue)) (e : Expr) : Option SemValue :=
  Core.Expression.eval f (bindStore bs) e

/-- The API term `e` evaluates to `true`. -/
@[expose] def apiHolds (f : Fac) (bs : List (String × SemValue)) (e : Expr) : Prop :=
  apiEval f bs e = some (HasBool.ttVal (P := Core.Expression) f)

/-- The API term `e` evaluates to `false`. -/
@[expose] def apiFails (f : Fac) (bs : List (String × SemValue)) (e : Expr) : Prop :=
  apiEval f bs e = some (HasBool.ffVal (P := Core.Expression) f)

/-- `v` is a value of the monomorphic type `t`. -/
@[expose] def IsOfTy (f : Fac) (v : SemValue) (t : LMonoTy) : Prop :=
  HasVal.valueOfTy (P := Core.Expression) f v (.forAll [] t)

/-- The field constant `C.f` of the field `r`, of sort `Field t`. -/
@[expose] def fieldConst (r : FieldRef) (t : LMonoTy) : Expr :=
  .op Core.coreLoc ⟨s!"{r.owner}.{r.field}", ()⟩ (some (fieldTy t))

/-- The tag constant `C$Tag` of the composite `C`. -/
@[expose] def tagConst (c : TypeName) : Expr := .op Core.coreLoc ⟨s!"{c}$Tag", ()⟩ (some tagTy)

/-- The null reference `Null`. -/
@[expose] def nullRef : Expr := .op Core.coreLoc ⟨"Null", ()⟩ (some refTy)

/-- `Heap.read(h, o, f)` at field type `t`. -/
@[expose] def readT (t : LMonoTy) (h o fld : Expr) : Expr :=
  apiCall "Heap.read" [heapTy, refTy, fieldTy t] t [h, o, fld]

/-- `Heap.write(h, o, f, v)` at field type `t`. -/
@[expose] def writeT (t : LMonoTy) (h o fld v : Expr) : Expr :=
  apiCall "Heap.write" [heapTy, refTy, fieldTy t, t] heapTy [h, o, fld, v]

/-- `Heap.allocated(h, o)`. -/
@[expose] def allocatedT (h o : Expr) : Expr :=
  apiCall "Heap.allocated" [heapTy, refTy] .bool [h, o]

/-- `Ref.tag(o)`. -/
@[expose] def tagOfT (o : Expr) : Expr := apiCall "Ref.tag" [refTy] tagTy [o]

/-- `Ref..isObj(o)`: `o` is not `Null`. -/
@[expose] def isObjT (o : Expr) : Expr := apiCall "Ref..isObj" [refTy] .bool [o]

/-- `Obj(a, t)`. -/
@[expose] def objT (a t : Expr) : Expr := apiCall "Obj" [.int, tagTy] refTy [a, t]

/-- `Field.id(f)` at field type `t`. -/
@[expose] def fieldIdT (t : LMonoTy) (fld : Expr) : Expr :=
  apiCall "Field.id" [fieldTy t] fieldIdTy [fld]

/-- `Heap.grows(h0, h1)`. -/
@[expose] def growsT (h0 h1 : Expr) : Expr := apiCall "Heap.grows" [heapTy, heapTy] .bool [h0, h1]

/-- `Heap.onlyModifies(h0, h1, L)`. -/
@[expose] def onlyModifiesT (h0 h1 l : Expr) : Expr :=
  apiCall "Heap.onlyModifies" [heapTy, heapTy, locsTy] .bool [h0, h1, l]

/-- `Locs.mem(L, o, k)`. -/
@[expose] def locsMemT (l o k : Expr) : Expr :=
  apiCall "Locs.mem" [locsTy, refTy, fieldIdTy] .bool [l, o, k]

/-- `Locs.at(p, k)`. -/
@[expose] def locsAtT (p k : Expr) : Expr := apiCall "Locs.at" [refTy, fieldIdTy] locsTy [p, k]

/-- `Locs.object(p)`: every field of `p`. -/
@[expose] def locsObjectT (p : Expr) : Expr := apiCall "Locs.object" [refTy] locsTy [p]

/-- `Locs.none()`: no location. -/
@[expose] def locsNoneT : Expr := .op Core.coreLoc ⟨"Locs.none", ()⟩ (some locsTy)

/-- The monomorphic type of a field, erased. -/
@[expose] def fieldMonoTy (Γ : UnorderedProgram) (d : FieldDecl) : LMonoTy :=
  match d.ty with
  | .forAll _ t => eraseMono Γ t

/-! ## Lawful models of references and of the heap API

The factory interprets the datatypes `Ref` and `Tag` and the heap API's operations. These
predicates state what the relation may assume of that interpretation: the datatype laws,
and the heap API's laws (`Heap.nullNotAllocated`, the definition of `Heap.grows`,
`Heap.onlyModifies_refl`, `Heap.onlyModifies_trans`, `Locs.mem_at`, `Locs.mem_object`,
`Heap.frame`, `Heap.readWriteSame`, `Heap.writeOnlyModifies`, `Heap.writeKeepsAllocated`)
at the type of every field of the program, and `Locs.mem_none`. A law over a term
built from another (`Heap.read(Heap.write(h, …), …)`) is stated over the value of the
inner term. They do not fix the interpretation: any model satisfying them is allowed. -/

/-- The fields of the composites of `Γ`, each with its declaration. -/
@[expose] def programFields (Γ : UnorderedProgram) : List (FieldRef × FieldDecl) :=
  Γ.composites.flatMap fun c => c.fields.map fun d => (⟨c.name, d.name⟩, d)

/-- The names of the reference datatypes' functions that the relation uses. -/
@[expose] def refTagNames (Γ : UnorderedProgram) : List String :=
  ["Null", "Obj", "Ref..isObj", "Ref.tag"] ++ Γ.composites.map fun c => s!"{c.name}$Tag"

/-- The names of the heap API's functions that the relation uses, with the field
constants of `Γ`. -/
@[expose] def heapApiNames (Γ : UnorderedProgram) : List String :=
  ["Heap.read", "Heap.write", "Heap.allocated", "Heap.grows", "Heap.onlyModifies", "Field.id",
    "Locs.mem", "Locs.none", "Locs.at", "Locs.object"] ++
    (programFields Γ).map fun (r, _) => s!"{r.owner}.{r.field}"

/-- The factory `f` models the references of `Γ`: `Ref = Null | Obj (id : int) (tag : Tag)`,
and `Tag` has one constant `C$Tag` per composite `C`, all distinct. `Tag` may have other
values; that the objects a run allocates have the tag of a composite is an invariant of the
run's heaps (`WellTagged`), not a law of the model. -/
structure RefTagModel (Γ : UnorderedProgram) (f : Fac) : Prop where
  /-- The functions are declared. -/
  declared : ∀ n ∈ refTagNames Γ, n ∈ f.factory
  /-- Distinct composites have distinct tags. -/
  tagsDistinct : ∀ c ∈ Γ.composites, ∀ d ∈ Γ.composites, c.name ≠ d.name →
    apiFails f [] (.eq Core.coreLoc (tagConst c.name) (tagConst d.name))
  /-- `Null` is no object. -/
  nullNotObj : apiFails f [] (isObjT nullRef)
  /-- `Obj(a, t)` is an object. -/
  objIsObj : ∀ a t, IsOfTy f a .int → IsOfTy f t tagTy →
    apiHolds f [("$a", a), ("$t", t)] (isObjT (objT (apiVar "$a") (apiVar "$t")))
  /-- The tag of `Obj(a, t)` is `t`. -/
  tagOfObj : ∀ a t, IsOfTy f a .int → IsOfTy f t tagTy →
    apiHolds f [("$a", a), ("$t", t)]
      (.eq Core.coreLoc (tagOfT (objT (apiVar "$a") (apiVar "$t"))) (apiVar "$t"))
  /-- A reference that is no object is `Null`. -/
  refCases : ∀ o, IsOfTy f o refTy → apiFails f [("$o", o)] (isObjT (apiVar "$o")) →
    apiHolds f [("$o", o)] (.eq Core.coreLoc (apiVar "$o") nullRef)

/-- The factory `f` is a lawful model of the heap API at the fields of `Γ`. -/
structure HeapApiModel (Γ : UnorderedProgram) (f : Fac) : Prop where
  /-- The functions and the field constants are declared. -/
  declared : ∀ n ∈ heapApiNames Γ, n ∈ f.factory
  /-- `Locs.mem_none`: `Locs.none()` holds no location. -/
  memNone : ∀ o k, IsOfTy f o refTy → IsOfTy f k fieldIdTy →
    apiFails f [("$o", o), ("$k", k)] (locsMemT locsNoneT (apiVar "$o") (apiVar "$k"))
  /-- `Null` is never allocated. -/
  nullNotAllocated : ∀ h, IsOfTy f h heapTy →
    apiFails f [("$h", h)] (allocatedT (apiVar "$h") nullRef)
  /-- `Heap.grows(h0, h1)`: every reference allocated in `h0` is allocated in `h1`. -/
  grows : ∀ h0 h1, IsOfTy f h0 heapTy → IsOfTy f h1 heapTy →
    (apiHolds f [("$h", h0), ("$h'", h1)] (growsT (apiVar "$h") (apiVar "$h'")) ↔
      ∀ o, IsOfTy f o refTy →
        apiHolds f [("$h", h0), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o")) →
        apiHolds f [("$h", h1), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o")))
  /-- `Heap.onlyModifies(h, h, L)`. -/
  onlyModifiesRefl : ∀ h L, IsOfTy f h heapTy → IsOfTy f L locsTy →
    apiHolds f [("$h", h), ("$h'", h), ("$L", L)]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L"))
  /-- `Heap.onlyModifies` composes when the second set is included in the first. -/
  onlyModifiesTrans : ∀ h0 h1 h2 L M, IsOfTy f h0 heapTy → IsOfTy f h1 heapTy →
    IsOfTy f h2 heapTy → IsOfTy f L locsTy → IsOfTy f M locsTy →
    apiHolds f [("$h", h0), ("$h'", h1), ("$L", L)]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L")) →
    apiHolds f [("$h", h1), ("$h'", h2), ("$L", M)]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L")) →
    (∀ o k, IsOfTy f o refTy → IsOfTy f k fieldIdTy →
      apiHolds f [("$L", M), ("$o", o), ("$k", k)]
        (locsMemT (apiVar "$L") (apiVar "$o") (apiVar "$k")) →
      apiHolds f [("$L", L), ("$o", o), ("$k", k)]
        (locsMemT (apiVar "$L") (apiVar "$o") (apiVar "$k"))) →
    apiHolds f [("$h", h0), ("$h'", h2), ("$L", L)]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L"))
  /-- `Locs.mem(Locs.at(p, j), o, k)` holds exactly when `o == p` and `k == j`. -/
  memAt : ∀ p j o k, IsOfTy f p refTy → IsOfTy f j fieldIdTy → IsOfTy f o refTy →
    IsOfTy f k fieldIdTy →
    (apiHolds f [("$p", p), ("$j", j), ("$o", o), ("$k", k)]
        (locsMemT (locsAtT (apiVar "$p") (apiVar "$j")) (apiVar "$o") (apiVar "$k")) ↔
      apiHolds f [("$p", p), ("$o", o)] (.eq Core.coreLoc (apiVar "$o") (apiVar "$p")) ∧
        apiHolds f [("$j", j), ("$k", k)] (.eq Core.coreLoc (apiVar "$k") (apiVar "$j")))
  /-- `Locs.mem(Locs.object(p), o, k)` holds exactly when `o == p`. -/
  memObject : ∀ p o k, IsOfTy f p refTy → IsOfTy f o refTy → IsOfTy f k fieldIdTy →
    (apiHolds f [("$p", p), ("$o", o), ("$k", k)]
        (locsMemT (locsObjectT (apiVar "$p")) (apiVar "$o") (apiVar "$k")) ↔
      apiHolds f [("$p", p), ("$o", o)] (.eq Core.coreLoc (apiVar "$o") (apiVar "$p")))
  /-- Distinct fields have distinct ids. -/
  fieldIdsDistinct : ∀ r d, (r, d) ∈ programFields Γ → ∀ r' d', (r', d') ∈ programFields Γ →
    r ≠ r' →
    apiFails f [] (.eq Core.coreLoc (fieldIdT (fieldMonoTy Γ d) (fieldConst r (fieldMonoTy Γ d)))
      (fieldIdT (fieldMonoTy Γ d') (fieldConst r' (fieldMonoTy Γ d'))))
  /-- `Heap.frame`: a field outside the modified locations keeps its value. -/
  frame : ∀ r d, (r, d) ∈ programFields Γ → ∀ h0 h1 L o, IsOfTy f h0 heapTy →
    IsOfTy f h1 heapTy → IsOfTy f L locsTy → IsOfTy f o refTy →
    apiHolds f [("$h", h0), ("$h'", h1), ("$L", L)]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L")) →
    apiFails f [("$L", L), ("$o", o)] (locsMemT (apiVar "$L") (apiVar "$o")
      (fieldIdT (fieldMonoTy Γ d) (fieldConst r (fieldMonoTy Γ d)))) →
    apiEval f [("$h", h1), ("$o", o)]
        (readT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))) =
      apiEval f [("$h", h0), ("$o", o)]
        (readT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d)))
  /-- `Heap.readWriteSame`: a field reads the value last written to it. -/
  readWriteSame : ∀ r d, (r, d) ∈ programFields Γ → ∀ h o w h', IsOfTy f h heapTy →
    IsOfTy f o refTy → IsOfTy f w (fieldMonoTy Γ d) →
    apiEval f [("$h", h), ("$o", o), ("$w", w)]
      (writeT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))
        (apiVar "$w")) = some h' →
    apiEval f [("$h", h'), ("$o", o)]
      (readT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))) =
      some w
  /-- `Heap.writeOnlyModifies`: a write modifies only its location. -/
  writeOnlyModifies : ∀ r d, (r, d) ∈ programFields Γ → ∀ h o w h', IsOfTy f h heapTy →
    IsOfTy f o refTy → IsOfTy f w (fieldMonoTy Γ d) →
    apiEval f [("$h", h), ("$o", o), ("$w", w)]
      (writeT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))
        (apiVar "$w")) = some h' →
    apiHolds f [("$h", h), ("$h'", h'), ("$o", o)] (onlyModifiesT (apiVar "$h") (apiVar "$h'")
      (locsAtT (apiVar "$o") (fieldIdT (fieldMonoTy Γ d) (fieldConst r (fieldMonoTy Γ d)))))
  /-- `Heap.writeKeepsAllocated`: a write allocates and frees nothing. -/
  writeKeepsAllocated : ∀ r d, (r, d) ∈ programFields Γ → ∀ h o w h' p,
    IsOfTy f h heapTy → IsOfTy f o refTy → IsOfTy f w (fieldMonoTy Γ d) →
    IsOfTy f p refTy →
    apiEval f [("$h", h), ("$o", o), ("$w", w)]
      (writeT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))
        (apiVar "$w")) = some h' →
    apiEval f [("$h", h'), ("$o", p)] (allocatedT (apiVar "$h") (apiVar "$o")) =
      apiEval f [("$h", h), ("$o", p)] (allocatedT (apiVar "$h") (apiVar "$o"))

/-- Every reference allocated in the heap `h` has the tag of a composite of `Γ`. The laws of a
model do not imply it, since `Tag` may have other values; the heap a run starts from has it
(`CortexInitEnvWF.entryHeap`), and allocation and field writes keep it. -/
@[expose] def WellTagged (Γ : UnorderedProgram) (f : Fac) (h : SemValue) : Prop :=
  ∀ o, IsOfTy f o refTy →
    apiHolds f [("$h", h), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o")) →
    ∃ c ∈ Γ.composites,
      apiHolds f [("$o", o)] (.eq Core.coreLoc (tagOfT (apiVar "$o")) (tagConst c.name))

/-- The value `v` is a safe reference in the heap `h`: if it is a reference, it is `Null` or
allocated in `h`. A value of another sort is safe. -/
@[expose] def SafeRef (f : Fac) (h v : SemValue) : Prop :=
  IsOfTy f v refTy →
    apiHolds f [("$o", v)] (.eq Core.coreLoc (apiVar "$o") nullRef) ∨
      apiHolds f [("$h", h), ("$o", v)] (allocatedT (apiVar "$h") (apiVar "$o"))

/-- Every value the store `σ` binds is a safe reference in the heap `h`. -/
@[expose] def StoreSafe (f : Fac) (h : SemValue) (σ : Store) : Prop :=
  ∀ x v, σ x = some v → SafeRef f h v

/-- The heap `h` is closed: every field `r` of `Γ`, with the declaration `d` that a field
access of `r` reads (`findField?`), at every reference, allocated or not, holds a safe
reference in `h`. -/
@[expose] def HeapClosed (Γ : UnorderedProgram) (f : Fac) (h : SemValue) : Prop :=
  ∀ r d, Γ.findField? r = some d → ∀ o w, IsOfTy f o refTy →
    apiEval f [("$h", h), ("$o", o)]
      (readT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))) =
      some w →
    SafeRef f h w

/-- The reserved name under which the initial store of a run binds the heap the run starts
from. -/
@[expose] def entryHeapVar : Core.Expression.Ident := ⟨"$entryHeap", ()⟩

/-- The heap a run from the store `σ` starts from: the value of `$entryHeap`; a Boolean if it
is unbound, which `CortexInitEnvWF.entryHeap` excludes. -/
@[expose] def entryHeap (f : Fac) (σ : Store) : SemValue :=
  (σ entryHeapVar).getD (SemValue.ofBool f.model.tcInterp false)

/-! ## States, outcomes, events -/

/-- A Cortex state: an environment and a heap. -/
structure CState where
  /-- The store and the factory. -/
  env : Imperative.Env Core.Expression
  /-- The heap, a value of the API's sort `Heap`. -/
  heap : SemValue

/-- The outcome of a command: normal, or an exception with its value. -/
inductive COutcome where
  | normal
  | exn (v : SemValue)

/-- An event of a Cortex run: a Core event, or an exception that escapes a procedure
without `throws`, with the factory and store where it escaped, the raising command's
metadata and a summary of the failed property. -/
inductive CEvent where
  | std (e : Event Core.Expression)
  | uncaught (f : Fac) (σ : Store) (md : MD) (summary : String)

/-- The dynamic class of a reference `v`: the first composite `C` of `Γ` such that `v`
is an object with tag `C$Tag`; `none` for `Null` and for a value that is no reference. -/
@[expose] noncomputable def semDynType (Γ : UnorderedProgram) (f : Fac) (v : SemValue) :
    Option TypeName :=
  open Classical in
  (Γ.composites.find? fun c =>
    decide (apiHolds f [("$o", v)] (isObjT (apiVar "$o")) ∧
      apiHolds f [("$o", v)] (.eq Core.coreLoc (tagOfT (apiVar "$o")) (tagConst c.name)))).map (·.name)

/-! ## Constraint checks

A variable of a constrained type holds a value of the type's base type (`eraseMono`), and
the type's constraint is an event at the places where `LowerCTE` puts it: asserted after a
deterministic write and before a call on the arguments of constrained parameters, assumed
after a nondeterministic write and on the results of a call, assumed of the inputs at
procedure entry and asserted of the outputs at a normal return. -/

/-- The constrained type of `Γ` that the type `t` names. -/
@[expose] def constrainedName? (Γ : UnorderedProgram) (t : LTy) : Option String :=
  (conTyName? t).filter fun n => Γ.constrained.any (·.name == n)

/-- The variable `x` with its type name when that is a constrained type of `Γ`, added in
front of `m`. -/
@[expose] def addConstrainedVar (Γ : UnorderedProgram) (m : List (String × String))
    (x : Core.Expression.Ident) (t : LTy) : List (String × String) :=
  match constrainedName? Γ t with
  | some n => (x.name, n) :: m
  | none => m

/-- The variables among the parameters `ps` and the `init`s of the body `b` whose type is a
constrained type of `Γ`, each with that type and the last binding of a name first, as
`LowerCTE.varTypes` collects them. -/
@[expose] def constrainedVars (Γ : UnorderedProgram) (ps : List (Core.Expression.Ident × LTy))
    (b : Option Body) : List (String × String) :=
  let params := ps.foldl (fun m (x, t) => addConstrainedVar Γ m x t) []
  match b with
  | none => params
  | some b => b.cfg.blocks.foldl (fun m (_, blk) => blk.cmds.foldl (fun m c =>
      match c with
      | .cmd (.init x t _ _) => addConstrainedVar Γ m x t
      | _ => m) m) params

/-- The check of the constraint of the constrained type `t` on `e`, as `LowerCTE.checkOf`:
an assertion of its checked parts when `assert`, an assumption of all of them otherwise,
and nothing when there is nothing to check. -/
@[expose] def checkOf (Γ : UnorderedProgram) (assert : Bool) (t : String) (e : Expr) (md : MD) :
    List (Cmd Core.Expression) :=
  match pred Γ.constrained t e (checkedOnly := assert) with
  | none => []
  | some p =>
    if assert then [.assert s!"constraint_{t}" p md] else [.assume s!"constraint_{t}" p md]

/-- The check of the constraint of the type that `vars` gives the variable `x`. -/
@[expose] def checkVar (Γ : UnorderedProgram) (vars : List (String × String)) (assert : Bool)
    (x : Core.Expression.Ident) (md : MD) : List (Cmd Core.Expression) :=
  match vars.lookup x.name with
  | some t => checkOf Γ assert t (mkFvar x.name) md
  | none => []

/-- The constrained types of the inputs and of the outputs of the procedure `q`, the last
one of that name, as `LowerCTE` reads a callee's signature. -/
@[expose] def procConstrained (Γ : UnorderedProgram) (q : ProcName) :
    List (Option String) × List (Option String) :=
  match Γ.procedures.reverse.find? (·.name == q) with
  | some p => (p.inputs.map (constrainedName? Γ ·.2), p.outputs.map (constrainedName? Γ ·.2))
  | none => ([], [])

/-- A check `e` as the check `$v || e`, which holds when the Boolean variable `v` does. -/
@[expose] def guardCheck (v : String) : Cmd Core.Expression → Cmd Core.Expression
  | .assert l e md => .assert l (mkCall "Bool.Or" [mkFvar v, e]) md
  | .assume l e md => .assume l (mkCall "Bool.Or" [mkFvar v, e]) md
  | c => c

/-- The checks before a call of `q` with arguments `args`: an assertion of the constraint
of each constrained input on its argument. -/
@[expose] def callPreChecks (Γ : UnorderedProgram) (q : ProcName) (args : List Expr) (md : MD) :
    List (Cmd Core.Expression) :=
  ((procConstrained Γ q).1.zip args).flatMap fun (t?, a) =>
    match t? with
    | some t => checkOf Γ true t a md
    | none => []

/-- The checks after a call of `q` into `lhs`, with the caller's constrained variables
`vars`: for each result, an assumption of the constraint of the callee's output type, and
an assertion of the constraint of the result variable's own type when that differs; all
guarded by `$callThrown` when the call writes it, as after `LowerExceptions`. -/
@[expose] def callPostChecks (Γ : UnorderedProgram) (vars : List (String × String))
    (lhs : List Core.Expression.Ident) (q : ProcName) (md : MD) : List (Cmd Core.Expression) :=
  let post := ((procConstrained Γ q).2.zip lhs).flatMap fun (t?, x) =>
    (match t? with
      | some t => checkOf Γ false t (mkFvar x.name) md
      | none => []) ++
    (if vars.lookup x.name == t? then [] else checkVar Γ vars true x md)
  if lhs.any (·.name == "$callThrown") then post.map (guardCheck "$callThrown") else post

/-- A base command followed by its constraint check: an assertion after a deterministic
write, an assumption after a nondeterministic one. -/
@[expose] def checkedBaseCmd (Γ : UnorderedProgram) (vars : List (String × String)) :
    Cmd Core.Expression → List (Cmd Core.Expression)
  | c@(.init x _ (.det _) md) | c@(.set x (.det _) md) => c :: checkVar Γ vars true x md
  | c@(.init x _ .nondet md) | c@(.set x .nondet md) => c :: checkVar Γ vars false x md
  | c => [c]

/-- A command with the constraint checks `LowerCTE.lowerCmd` puts around it, for the
constrained variables `vars` of the running procedure. A type test of a constrained type
is the test of its constraint, and a cast is an assignment followed by the cast's check. -/
@[expose] def checkedCmd (Γ : UnorderedProgram) (vars : List (String × String)) :
    IRCmd → List IRCmd
  | .cmd c => (checkedBaseCmd Γ vars c).map .cmd
  | c@(.instanceOf x o t md) =>
    match conTyName? t >>= fun n => pred Γ.constrained n o with
    | some test => .cmd (.set x (.det test) md) :: (checkVar Γ vars true x md).map .cmd
    | none => [c]
  | c@(.call lhs q args md) =>
    (callPreChecks Γ q args md).map .cmd ++ [c] ++ (callPostChecks Γ vars lhs q md).map .cmd
  | c@(.virtualCall lhs o meth args md) =>
    (callPreChecks Γ (implName o meth) args md).map .cmd ++ [c] ++
      (callPostChecks Γ vars lhs (implName o meth) md).map .cmd
  | .cast x t e mode md =>
    .cmd (.set x (.det e) md) :: (checkOf Γ (mode == .check) t (mkFvar x.name) md ++
      (if vars.lookup x.name == some t then [] else checkVar Γ vars true x md)).map .cmd
  | c => [c]

/-- The constrained variables of the procedure `p` with the outputs left out, whose writes
the body checks. -/
@[expose] def procVars (Γ : UnorderedProgram) (p : Procedure) : List (String × String) :=
  (constrainedVars Γ (p.inputs ++ p.outputs) p.body).filter fun (x, _) =>
    !(p.outputs.map (·.1.name)).contains x

/-- The assumptions of the constraints of the inputs of `p` at its entry. -/
@[expose] def entryChecks (Γ : UnorderedProgram) (p : Procedure) : List (Cmd Core.Expression) :=
  p.inputs.flatMap fun (x, _) =>
    checkVar Γ (constrainedVars Γ (p.inputs ++ p.outputs) p.body) false x p.md

/-- The assertions of the constraints of the outputs of `p` at a normal return, guarded by
`$thrown` when `p` has that output. -/
@[expose] def exitChecks (Γ : UnorderedProgram) (p : Procedure) : List (Cmd Core.Expression) :=
  p.outputs.flatMap fun (x, _) =>
    (checkVar Γ (constrainedVars Γ (p.inputs ++ p.outputs) p.body) true x p.md).map fun c =>
      if p.outputs.any (·.1.name == "$thrown") then guardCheck "$thrown" c else c

/-- The events of the checks `cs` at factory `f` and store `σ`. -/
@[expose] def checkEvents (Γ : UnorderedProgram) (cs : List (Cmd Core.Expression)) (f : Fac)
    (σ : Store) : List CEvent :=
  cs.flatMap fun c => (Cmd.emittedEvents (P := Core.Expression) (eraseCmd Γ c) f σ).map .std

/-! ## Frames and configurations -/

/-- The running procedure: its body, its `throws` clause, its postconditions, the entry
values its postconditions read (`entryOld`), the constrained variables whose writes
its body checks, and the checks of a normal return. -/
structure Fr where
  body : Body
  throws : Option TypeName
  ensures : List Postcondition
  old : Store
  vars : List (String × String)
  exits : List (Cmd Core.Expression)

/-- The commands the relation runs for the block `blk` of the frame `fr`: each command with
its constraint checks, and the checks of a normal return in a block that ends the
procedure. -/
@[expose] def Fr.blockCmds (Γ : UnorderedProgram) (fr : Fr) (blk : LBlock) : List IRCmd :=
  blk.cmds.flatMap (checkedCmd Γ fr.vars) ++
    match blk.transfer with
    | .finish _ => fr.exits.map .cmd
    | .condGoto .. => []

/-- A Cortex configuration. Only `terminal` lacks a heap, so that a terminal
configuration is determined by its environment. -/
inductive CConfig where
  /-- Before fetching the block `t`. -/
  | atBlock (fr : Fr) (t : Label) (s : CState)
  /-- Inside the block `t`, with its remaining commands and its transfer. -/
  | inBlock (fr : Fr) (t : Label) (cs : List IRCmd) (tr : DetTransferCmd Label Core.Expression)
      (s : CState)
  /-- The procedure returned normally. -/
  | returned (s : CState)
  /-- The procedure ended with the exception `v`. -/
  | raised (s : CState) (v : SemValue)
  /-- The run ended. -/
  | terminal (ρ : Imperative.Env Core.Expression)

/-- The environment of a configuration. -/
@[expose] def CConfig.getEnv : CConfig → Imperative.Env Core.Expression
  | .atBlock _ _ s | .inBlock _ _ _ _ s | .returned s | .raised s _ => s.env
  | .terminal ρ => ρ

/-- The pairs of a result variable in `lhs` and the output of `p` it receives that is also
an input of `p`: on an exception these are the results a call still copies back. -/
@[expose] def inoutResults (p : Procedure) (lhs : List Core.Expression.Ident) :
    List (Core.Expression.Ident × Core.Expression.Ident) :=
  (lhs.zip (p.outputs.map Prod.fst)).filter fun (_, o) => p.inputs.any (·.1 == o)

/-- The postcondition events of a normal return at state `s`: an assertion per
postcondition, in order, with the postcondition's metadata. -/
@[expose] def ensuresEvents (Γ : UnorderedProgram) (fr : Fr) (s : CState) : List CEvent :=
  fr.ensures.map fun post =>
    .std (.assert { factory := s.env.factory, store := postStore fr.old s.env.store,
                    label := post.label, expr := eraseExpr Γ post.cond, metadata := post.md })

/-- The precondition events of a call to `p` at metadata `md`, at the callee's entry
store `σ₀`: an assertion per precondition. -/
@[expose] def requiresEvents (Γ : UnorderedProgram) (p : Procedure) (md : MD) (f : Fac)
    (σ₀ : Store) : List CEvent :=
  p.requires.map fun pre =>
    .std (.assert { factory := f, store := σ₀, label := s!"requires_{p.name}",
                    expr := eraseExpr Γ pre.cond, metadata := preconditionMd md pre })

/-- The summary of the failed property when the exception of `c` escapes a procedure
without `throws`, as `LowerExceptions` words it. -/
@[expose] def raiseSummary (Γ : UnorderedProgram) : IRCmd → String
  | .throw .. => "uncaught exception is not thrown"
  | .call _ q _ _ => callSummary q
  | .virtualCall _ o m _ _ => callSummary (implName o m)
  | _ => ""
where
  callSummary (q : ProcName) : String :=
    match (Γ.findProcedure? q).bind (·.throws) with
    | some ty => s!"call does not throw an uncaught '{ty}'"
    | none => ""

/-! ## Step relation -/

/-- One step of a Cortex configuration, with the command relation `EvalCmd` as a
parameter. A command step updates the state and, on an exception, routes it to the
covering handler, to `raised`, or (without `throws`) to an `uncaught` event and a normal
return. No rule applies to an exception whose value has no dynamic class. -/
inductive StepCortex (Γ : UnorderedProgram)
    (EvalCmd : CState → IRCmd → CState → COutcome → List CEvent → Prop) :
    CConfig → List CEvent → CConfig → Prop where
  /-- Fetch the block `t`, its commands with their constraint checks. -/
  | fetch {fr t s blk} :
      List.lookup t fr.body.cfg.blocks = some blk →
      StepCortex Γ EvalCmd (.atBlock fr t s) [] (.inBlock fr t (fr.blockCmds Γ blk) blk.transfer s)
  /-- A command that ends normally. -/
  | cmd_normal {fr t c cs tr s s' evs} :
      EvalCmd s c s' .normal evs →
      StepCortex Γ EvalCmd (.inBlock fr t (c :: cs) tr s) evs (.inBlock fr t cs tr s')
  /-- An exception caught by the handler `h`, its binder set to the exception. -/
  | cmd_caught {fr t c cs tr s s' v evs ty h} :
      EvalCmd s c s' (.exn v) evs →
      semDynType Γ s.env.factory v = some ty →
      fr.body.handlerFor? Γ t (tcon ty) = some h →
      StepCortex Γ EvalCmd (.inBlock fr t (c :: cs) tr s) evs
        (.atBlock fr h.target ⟨{ s'.env with store := s'.env.store.update h.binder v }, s'.heap⟩)
  /-- An uncaught exception in a procedure with `throws`. -/
  | cmd_uncaught_throws {fr t c cs tr s s' v evs ty th} :
      EvalCmd s c s' (.exn v) evs →
      semDynType Γ s.env.factory v = some ty →
      fr.body.handlerFor? Γ t (tcon ty) = none →
      fr.throws = some th →
      StepCortex Γ EvalCmd (.inBlock fr t (c :: cs) tr s) evs (.raised s' v)
  /-- An uncaught exception in a procedure without `throws`: an `uncaught` event, and a
  normal return. -/
  | cmd_uncaught_nothrows {fr t c cs tr s s' v evs ty} :
      EvalCmd s c s' (.exn v) evs →
      semDynType Γ s.env.factory v = some ty →
      fr.body.handlerFor? Γ t (tcon ty) = none →
      fr.throws = none →
      StepCortex Γ EvalCmd (.inBlock fr t (c :: cs) tr s)
        (evs ++ [.uncaught s'.env.factory s'.env.store (IRCmd.md c) (raiseSummary Γ c)])
        (.returned s')
  /-- A conditional jump whose condition is true. -/
  | goto_true {fr t c lt lf md s} :
      ceval Γ s.env.factory s.env.store c = some (HasBool.ttVal s.env.factory) →
      StepCortex Γ EvalCmd (.inBlock fr t [] (.condGoto c lt lf md) s) [] (.atBlock fr lt s)
  /-- A conditional jump whose condition is false. -/
  | goto_false {fr t c lt lf md s} :
      ceval Γ s.env.factory s.env.store c = some (HasBool.ffVal s.env.factory) →
      StepCortex Γ EvalCmd (.inBlock fr t [] (.condGoto c lt lf md) s) [] (.atBlock fr lf s)
  /-- A normal return, asserting the postconditions. -/
  | finish {fr t md s} :
      StepCortex Γ EvalCmd (.inBlock fr t [] (.finish md) s) (ensuresEvents Γ fr s)
        (.returned s)
  /-- The end of a run that returned normally. -/
  | close {s} :
      StepCortex Γ EvalCmd (.returned s) [] (.terminal s.env)

/-! ## Command relation -/

/-- The result of a procedure body: a normal return or an exception. -/
inductive RunResult where
  | returned (s : CState)
  | raised (s : CState) (v : SemValue)

/-- The outputs of `p` that are not also inputs, which a call gives values of their
types; an output that is also an input holds the argument. -/
@[expose] def chosenOutputs (p : Procedure) : List (Core.Expression.Ident × Core.Expression.Ty) :=
  p.outputs.filter fun (x, _) => !p.inputs.any (·.1 == x)

/-- The callee's entry store `σ₀` of a call to `p` from store `σ`: the globals' values in
`σ`, the evaluated arguments at the inputs, each a value of the input's declared type, and
values of their declared types at the outputs that are not inputs (`chosenOutputs`), in the
empty store. -/
@[expose] def CallFrame (Γ : UnorderedProgram) (f : Fac) (σ : Store) (p : Procedure)
    (args : List Expr) (σ₀ : Store) : Prop :=
  ∃ gvals ins outs σG σI,
    ReadValues f σ (globalNames Γ) gvals ∧
    InitStates emptyStore (globalNames Γ) gvals σG ∧
    EvalExpressions f σ (args.map (eraseExpr Γ)) ins ∧
    List.Rel₂ (fun (xt : Core.Expression.Ident × Core.Expression.Ty) v =>
      HasVal.valueOfTy (P := Core.Expression) f v (eraseTy Γ xt.2)) p.inputs ins ∧
    InitStates σG (p.inputs.map Prod.fst) ins σI ∧
    List.Rel₂ (fun (xt : Core.Expression.Ident × Core.Expression.Ty) v =>
      HasVal.valueOfTy (P := Core.Expression) f v (eraseTy Γ xt.2)) (chosenOutputs p) outs ∧
    InitStates σI ((chosenOutputs p).map Prod.fst) outs σ₀

/-- The caller's store `σ'` after a call: `σ` with the globals' values in the callee's
final store `σE`. -/
@[expose] def GlobalsBack (Γ : UnorderedProgram) (f : Fac) (σ σE σ' : Store) : Prop :=
  ∃ gvals, ReadValues f σE (globalNames Γ) gvals ∧ UpdateStates σ (globalNames Γ) gvals σ'

/-- The frame of `p`'s body `b` entered at store `σ₀`. -/
@[expose] def procFrame (Γ : UnorderedProgram) (p : Procedure) (b : Body) (σ₀ : Store) : Fr :=
  ⟨b, p.throws, p.ensures, entryOld Γ (p.inputs.map Prod.fst) (p.outputs.map Prod.fst) σ₀,
    procVars Γ p, exitChecks Γ p⟩

/-- Allocation of a reference `v` of class `ty`, turning the heap `h` into `h'`: the
postconditions of the heap API's `Heap.new`, in order. `v` is unallocated in `h`
(`new_fresh`) and allocated in `h'` (`new_allocated`), has tag `ty$Tag` (`new_tag`), every
reference allocated in `h'` is allocated in `h` or is `v` (`new_exactly`, its `o == r` read as
equality of values), `h'` grows `h`
(`new_grows`), and no field changes (`new_noField`). -/
@[expose] def NewObj (f : Fac) (h : SemValue) (ty : TypeName) (v h' : SemValue) : Prop :=
  apiFails f [("$h", h), ("$o", v)] (allocatedT (apiVar "$h") (apiVar "$o")) ∧
  apiHolds f [("$h", h'), ("$o", v)] (allocatedT (apiVar "$h") (apiVar "$o")) ∧
  apiHolds f [("$o", v)] (.eq Core.coreLoc (tagOfT (apiVar "$o")) (tagConst ty)) ∧
  (∀ o, IsOfTy f o refTy →
    apiHolds f [("$h", h'), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o")) →
    apiHolds f [("$h", h), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o")) ∨ o = v) ∧
  apiHolds f [("$h", h), ("$h'", h')] (growsT (apiVar "$h") (apiVar "$h'")) ∧
  apiHolds f [("$h", h), ("$h'", h')] (onlyModifiesT (apiVar "$h") (apiVar "$h'") locsNoneT)

mutual

/-- One Cortex command: the state after it, its outcome and its events. -/
inductive EvalIRCmd (Γ : UnorderedProgram) :
    CState → IRCmd → CState → COutcome → List CEvent → Prop where
  /-- A base command, by `EvalCmdE` on its erasure, whose write is a safe reference; the
  heap is unchanged. -/
  | base {s c σ' evs} :
      EvalCmdE Core.Expression s.env.factory s.env.store (eraseCmd Γ c) σ' evs →
      (∀ x v, σ' x = some v → s.env.store x ≠ some v → SafeRef s.env.factory s.heap v) →
      EvalIRCmd Γ s (.cmd c) ⟨{ s.env with store := σ' }, s.heap⟩ .normal (evs.map .std)
  /-- Allocation of any fresh reference of class `ty`, written to a variable that holds a value
  of the reference's type. -/
  | new {s x ty md cd v h' σ'} :
      Γ.findComposite? ty = some cd →
      NewObj s.env.factory s.heap ty v h' →
      HasVal.valueOfStoredTy (P := Core.Expression) s.env.factory s.env.store x v →
      UpdateState Core.Expression s.env.store x v σ' →
      EvalIRCmd Γ s (.new x ty md) ⟨{ s.env with store := σ' }, h'⟩ .normal []
  /-- A field read of an allocated reference. -/
  | readField {s x obj r md v d w σ'} :
      ceval Γ s.env.factory s.env.store obj = some v →
      apiHolds s.env.factory [("$h", s.heap), ("$o", v)] (allocatedT (apiVar "$h") (apiVar "$o")) →
      Γ.findField? r = some d →
      apiEval s.env.factory [("$h", s.heap), ("$o", v)]
        (readT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d)))
        = some w →
      UpdateState Core.Expression s.env.store x w σ' →
      EvalIRCmd Γ s (.readField x obj r md) ⟨{ s.env with store := σ' }, s.heap⟩ .normal []
  /-- A field write of an allocated reference, with a value of the field's type that is a
  safe reference. -/
  | writeField {s obj r rhs md v w d h'} :
      ceval Γ s.env.factory s.env.store obj = some v →
      apiHolds s.env.factory [("$h", s.heap), ("$o", v)] (allocatedT (apiVar "$h") (apiVar "$o")) →
      ceval Γ s.env.factory s.env.store rhs = some w →
      SafeRef s.env.factory s.heap w →
      Γ.findField? r = some d →
      IsOfTy s.env.factory w (fieldMonoTy Γ d) →
      apiEval s.env.factory [("$h", s.heap), ("$o", v), ("$w", w)]
        (writeT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))
          (apiVar "$w")) = some h' →
      EvalIRCmd Γ s (.writeField obj r rhs md) ⟨s.env, h'⟩ .normal []
  /-- A type test of a reference's class; it reads no heap. -/
  | instanceOf {s x obj ty md v t mty σ'} :
      LTy.toMonoType? ty = some mty →
      ceval Γ s.env.factory s.env.store obj = some v →
      semDynType Γ s.env.factory v = some t →
      UpdateState Core.Expression s.env.store x
        (SemValue.ofBool s.env.factory.model.tcInterp (Γ.isSubtypeTy (tcon t) mty)) σ' →
      EvalIRCmd Γ s (.instanceOf x obj ty md) ⟨{ s.env with store := σ' }, s.heap⟩ .normal []
  /-- A throw of the value of `e`, a safe reference. -/
  | throw {s e md v} :
      ceval Γ s.env.factory s.env.store e = some v →
      SafeRef s.env.factory s.heap v →
      EvalIRCmd Γ s (.throw e md) s (.exn v) []
  /-- A call of the procedure `n`. -/
  | call {s lhs n args md s' o evs} :
      CallProc Γ s lhs n args md s' o evs →
      EvalIRCmd Γ s (.call lhs n args md) s' o evs
  /-- A virtual call, dispatched on the class of its receiver; it reads no heap. -/
  | virtualCall {s lhs owner meth r rs md v t s' o evs} :
      ceval Γ s.env.factory s.env.store r = some v →
      semDynType Γ s.env.factory v = some t →
      CallProc Γ s lhs (Γ.dispatch owner meth (tcon t)) (r :: rs) md s' o evs →
      EvalIRCmd Γ s (.virtualCall lhs owner meth (r :: rs) md) s' o evs

/-- A call of the procedure `n` from state `s`: the callee's preconditions and the
assumptions of the constraints of its inputs, then its body from its entry frame, then the
outputs and globals copied back. The callee's entry store holds only safe references: its
arguments and the values `CallFrame` chooses for its outputs. Each result written to a
target has the type of the value the target holds (`valueOfStoredTy`). -/
inductive CallProc (Γ : UnorderedProgram) :
    CState → List Core.Expression.Ident → ProcName → List Expr → MD →
      CState → COutcome → List CEvent → Prop where
  /-- The callee returned normally. -/
  | normal {s lhs n args md p σ₀ evs sE outs σL σ'} :
      Γ.findProcedure? n = some p →
      CallFrame Γ s.env.factory s.env.store p args σ₀ →
      StoreSafe s.env.factory s.heap σ₀ →
      RunBody Γ p ⟨⟨σ₀, s.env.factory⟩, s.heap⟩ evs (.returned sE) →
      lhs.Nodup →
      ReadValues s.env.factory sE.env.store (p.outputs.map Prod.fst) outs →
      List.Rel₂ (HasVal.valueOfStoredTy (P := Core.Expression) s.env.factory s.env.store)
        lhs outs →
      UpdateStates s.env.store lhs outs σL →
      GlobalsBack Γ s.env.factory σL sE.env.store σ' →
      CallProc Γ s lhs n args md ⟨{ s.env with store := σ' }, sE.heap⟩ .normal
        (requiresEvents Γ p md s.env.factory σ₀ ++
          checkEvents Γ (entryChecks Γ p) s.env.factory σ₀ ++ evs)
  /-- The callee ended with the exception `v`. The globals and the results of the outputs
  that are also inputs, the channel of a lowered global, are copied back; the other results
  keep their values. -/
  | raised {s lhs n args md p σ₀ evs sE v σG vals σ'} :
      Γ.findProcedure? n = some p →
      CallFrame Γ s.env.factory s.env.store p args σ₀ →
      StoreSafe s.env.factory s.heap σ₀ →
      RunBody Γ p ⟨⟨σ₀, s.env.factory⟩, s.heap⟩ evs (.raised sE v) →
      lhs.Nodup →
      GlobalsBack Γ s.env.factory s.env.store sE.env.store σG →
      ReadValues s.env.factory sE.env.store ((inoutResults p lhs).map Prod.snd) vals →
      List.Rel₂ (HasVal.valueOfStoredTy (P := Core.Expression) s.env.factory σG)
        ((inoutResults p lhs).map Prod.fst) vals →
      UpdateStates σG ((inoutResults p lhs).map Prod.fst) vals σ' →
      CallProc Γ s lhs n args md ⟨{ s.env with store := σ' }, sE.heap⟩ (.exn v)
        (requiresEvents Γ p md s.env.factory σ₀ ++
          checkEvents Γ (entryChecks Γ p) s.env.factory σ₀ ++ evs)

/-- A run of the body of `p` from its entry state `s₀` to a normal return or an
exception. -/
inductive RunBody (Γ : UnorderedProgram) :
    Procedure → CState → List CEvent → RunResult → Prop where
  /-- The body returned normally. -/
  | returned {p b s₀ evs sE} :
      p.body = some b →
      ReflTransTrace (StepCortex Γ (EvalIRCmd Γ))
        (.atBlock (procFrame Γ p b s₀.env.store) b.cfg.entry s₀) evs (.returned sE) →
      RunBody Γ p s₀ evs (.returned sE)
  /-- The body ended with the exception `v`. -/
  | raised {p b s₀ evs sE v} :
      p.body = some b →
      ReflTransTrace (StepCortex Γ (EvalIRCmd Γ))
        (.atBlock (procFrame Γ p b s₀.env.store) b.cfg.entry s₀) evs (.raised sE v) →
      RunBody Γ p s₀ evs (.raised sE v)

end

end -- public section

end Cortex.Sem
