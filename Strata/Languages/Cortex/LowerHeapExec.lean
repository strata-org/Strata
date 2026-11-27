/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module
public import Strata.Languages.Cortex.TypeCheck
public import Strata.Languages.Cortex.LowerComposites

namespace Cortex.LowerHeapExec

open Imperative Lambda

public section

def heapTy : String := "$Heap"
def objTy : String := "$Obj"
def fieldsTy : String := "$Fields"
def boxTy : String := "$Box"
def heapVar : String := "$heap"
def nextVar : String := "$next"

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩
def cid (n : String) : Core.CoreLParams.Identifier := ⟨n, ()⟩

def boxCtor (t : LMonoTy) : String := s!"$Box${mangle t}"
def boxField (t : LMonoTy) : String := s!"$val${mangle t}"
def box (t : LMonoTy) (e : Expr) : Expr := mkCall (boxCtor t) [e]
def unbox (t : LMonoTy) (e : Expr) : Expr := mkCall s!"{boxTy}..{boxField t}!" [e]

def hNil : Expr := mkOp "$HNil"
def fNil : Expr := mkOp "$FNil"
def mkObj (tag fs len : Expr) : Expr := mkCall "$MkObj" [tag, fs, len]
def objTag (o : Expr) : Expr := mkCall s!"{objTy}..$tag!" [o]
def objFields (o : Expr) : Expr := mkCall s!"{objTy}..$fields!" [o]
def objLen (o : Expr) : Expr := mkCall s!"{objTy}..$len!" [o]
def addr (r : Expr) : Expr := LowerComposites.refOf r
def heap : Expr := mkFvar heapVar
def next : Expr := mkFvar nextVar

def stuckObj : Expr := mkCall s!"{heapTy}..$hv!" [hNil]
def stuckInt : Expr := objLen stuckObj
def stuckFields : Expr := objFields stuckObj
def stuckBox : Expr := mkCall s!"{fieldsTy}..$fv!" [fNil]

def ite (c t e : Expr) : Expr := .ite Core.coreLoc c t e
def eq (a b : Expr) : Expr := .eq Core.coreLoc a b

def heapGet (h r : Expr) : Expr := mkCall "$heapGet" [h, r]
def heapPut (h r o : Expr) : Expr := mkCall "$heapPut" [h, r, o]
def fieldGet (fs k : Expr) : Expr := mkCall "$fieldGet" [fs, k]
def fieldPut (fs k v : Expr) : Expr := mkCall "$fieldPut" [fs, k, v]
def fieldSet (fs k v : Expr) : Expr := mkCall "$fieldSet" [fs, k, v]
def elemGet (fs k d : Expr) : Expr := mkCall "$elemGet" [fs, k, d]

def fn (name : String) (inputs : List (String × LMonoTy)) (output : LMonoTy) (body : Expr) :
    LFunc Core.CoreLParams :=
  LFunc.mk (cid name) (isRecursive := true) (inputs := inputs.map fun (x, t) => (cid x, t))
    (output := output) (body := some body) (attr := #[.inlineIfConstr 0])

def functions : List (LFunc Core.CoreLParams) :=
  let h := mkFvar "h"; let r := mkFvar "r"; let o := mkFvar "o"
  let fs := mkFvar "fs"; let k := mkFvar "k"; let v := mkFvar "v"; let d := mkFvar "d"
  let hk := mkCall s!"{heapTy}..$hk!" [h]
  let hv := mkCall s!"{heapTy}..$hv!" [h]
  let hrest := mkCall s!"{heapTy}..$hrest!" [h]
  let fk := mkCall s!"{fieldsTy}..$fk!" [fs]
  let fv := mkCall s!"{fieldsTy}..$fv!" [fs]
  let frest := mkCall s!"{fieldsTy}..$frest!" [fs]
  let hCons := fun a b c => mkCall "$HCons" [a, b, c]
  let fCons := fun a b c => mkCall "$FCons" [a, b, c]
  [ fn "$heapGet" [("h", tcon heapTy), ("r", .int)] (tcon objTy)
      (ite (eq hk r) hv (heapGet hrest r)),
    fn "$heapPut" [("h", tcon heapTy), ("r", .int), ("o", tcon objTy)] (tcon heapTy)
      (ite (mkCall "is$HNil" [h]) (hCons r o hNil)
        (ite (eq hk r) (hCons r o hrest) (hCons hk hv (heapPut hrest r o)))),
    fn "$fieldGet" [("fs", tcon fieldsTy), ("k", .int)] (tcon boxTy)
      (ite (eq fk k) fv (fieldGet frest k)),
    fn "$fieldPut" [("fs", tcon fieldsTy), ("k", .int), ("v", tcon boxTy)] (tcon fieldsTy)
      (ite (mkCall "is$FNil" [fs]) (fCons k v fNil)
        (ite (eq fk k) (fCons k v frest) (fCons fk fv (fieldPut frest k v)))),
    fn "$fieldSet" [("fs", tcon fieldsTy), ("k", .int), ("v", tcon boxTy)] (tcon fieldsTy)
      (ite (eq fk k) (fCons k v frest) (fCons fk fv (fieldSet frest k v))),
    fn "$elemGet" [("fs", tcon fieldsTy), ("k", .int), ("d", tcon boxTy)] (tcon boxTy)
      (ite (mkCall "is$FNil" [fs]) d
        (ite (eq fk k) fv (elemGet frest k d))) ]

def datatypes (boxTys : List LMonoTy) : List (LDatatype Unit) :=
  let boxCtors : List (LConstr Unit) := boxTys.map fun t =>
    { name := ⟨boxCtor t, ()⟩, args := [(⟨boxField t, ()⟩, t)] }
  let boxCtors := if boxCtors.isEmpty then [{ name := ⟨"$BoxNone", ()⟩, args := [] }] else boxCtors
  have hb : boxCtors.length != 0 := (by simp only [boxCtors]; split <;> simp_all)
  [ { name := boxTy, typeArgs := [], constrs := boxCtors, constrs_ne := hb },
    { name := fieldsTy, typeArgs := [],
      constrs := [{ name := ⟨"$FNil", ()⟩, args := [] },
                  { name := ⟨"$FCons", ()⟩,
                    args := [(⟨"$fk", ()⟩, .int), (⟨"$fv", ()⟩, tcon boxTy), (⟨"$frest", ()⟩, tcon fieldsTy)] }],
      constrs_ne := by simp },
    { name := objTy, typeArgs := [],
      constrs := [{ name := ⟨"$MkObj", ()⟩,
                    args := [(⟨"$tag", ()⟩, .int), (⟨"$fields", ()⟩, tcon fieldsTy), (⟨"$len", ()⟩, .int)] }],
      constrs_ne := by simp },
    { name := heapTy, typeArgs := [],
      constrs := [{ name := ⟨"$HNil", ()⟩, args := [] },
                  { name := ⟨"$HCons", ()⟩,
                    args := [(⟨"$hk", ()⟩, .int), (⟨"$hv", ()⟩, tcon objTy), (⟨"$hrest", ()⟩, tcon heapTy)] }],
      constrs_ne := by simp } ]

structure Info where
  prog : UnorderedProgram
  arrays : List LMonoTy
  tags : List TypeName
  fields : List FieldRef

def Info.tagOf (i : Info) (c : TypeName) : Expr := intLit ((i.tags.idxOf c : Nat) : Int)
def Info.fieldOf (i : Info) (f : FieldRef) : Expr := intLit ((i.fields.idxOf f : Nat) : Int)

def runtimeTy (prog : UnorderedProgram) (t : Core.Expression.Ty) : Except String LMonoTy :=
  TypeCheck.eraseTy prog t

partial def defaultOf (prog : UnorderedProgram) (t : Core.Expression.Ty) : Except String Expr :=
  match (t : LTy) with
  | .forAll [] t@(.tcons "Array" [_]) =>
    .ok (mkCall LowerComposites.compositeCtor [intLit (-1), LowerComposites.tagOf (LowerComposites.arrayTag t)])
  | .forAll [] (.tcons "int" []) => .ok (intLit 0)
  | .forAll [] (.tcons "bool" []) => .ok ff
  | .forAll [] (.tcons "string" []) => .ok (.const Core.valueLoc (.strConst ""))
  | .forAll [] (.tcons "real" []) => .ok (.const Core.valueLoc (.rationalConst 0))
  | .forAll [] (.bitvec n) => .ok (.const Core.valueLoc (.bitvecConst n 0))
  | .forAll [] (.tcons n []) =>
    if (prog.findComposite? n).isSome then
      .ok (mkCall LowerComposites.compositeCtor [intLit (-1), LowerComposites.tagOf n])
    else if n == LowerComposites.compositeTy || n.startsWith "$Any" then
      match prog.composites, prog.datatypes.find? (·.name == LowerComposites.typeTagTy) with
      | c :: _, _ => .ok (mkCall LowerComposites.compositeCtor [intLit (-1), LowerComposites.tagOf c.name])
      | [], some { constrs := tag :: _, .. } =>
        .ok (mkCall LowerComposites.compositeCtor [intLit (-1), mkOp tag.name.name])
      | [], _ => .error s!"no default value of type {n}"
    else match prog.constrained.find? (·.name == n) with
      | some c => match c.witness with
        | some w => .ok w
        | none => defaultOf prog c.base
      | none =>
        match prog.datatypes.find? (·.name == n) with
        | some d =>
          match d.constrs.find? (·.args.isEmpty) with
          | some c => .ok (mkOp c.name.name)
          | none => .error s!"no default value of type {n}"
        | none => .error s!"no default value of type {n}"
  | _ => .error s!"no default value of type {Std.format (t : LTy)}"

def objectFields (prog : UnorderedProgram) (t : LMonoTy) : List (FieldRef × Core.Expression.Ty) :=
  prog.composites.flatMap fun d =>
    if prog.isSubtypeTy t (tcon d.name) then d.fields.map fun f => (⟨d.name, f.name⟩, f.ty) else []

def elemKey (idx : Expr) : Expr := mkCall "Int.Sub" [intLit (-1), idx]

partial def elemDefault (prog : UnorderedProgram) (t : Core.Expression.Ty) : Except String Expr :=
  match (t : LTy) with
  | .forAll [] (.tcons n []) =>
    if (prog.findComposite? n).isSome then defaultOf prog t else
    match prog.constrained.find? (·.name == n) with
    | some c => elemDefault prog c.base
    | none => defaultOf prog t
  | _ => defaultOf prog t

def setTo (x : Core.Expression.Ident) (e : Expr) (md : MD) : IRCmd := .cmd (.set x (.det e) md)

def alloc (i : Info) (x : Core.Expression.Ident) (c : TypeName) (fs len : Expr) (md : MD) : List IRCmd :=
  [setTo x (mkCall LowerComposites.compositeCtor [next, LowerComposites.tagOf c]) md,
   setTo (ident heapVar) (heapPut heap next (mkObj (i.tagOf c) fs len)) md,
   setTo (ident nextVar) (mkCall "Int.Add" [next, intLit 1]) md]

def tagIn (tag : Expr) (tags : List TypeName) : Expr :=
  tags.foldr (fun n acc => mkCall "Bool.Or" [eq tag (LowerComposites.tagOf n), acc]) ff

def arraysBelow (i : Info) (t : LMonoTy) : List TypeName :=
  (i.arrays.filter fun a => i.prog.isSubtypeTy a t).map LowerComposites.arrayTag

def tagsBelow (i : Info) (t : LMonoTy) : List TypeName :=
  (i.prog.composites.filter fun c => i.prog.isSubtypeTy (tcon c.name) t).map (·.name) ++ arraysBelow i t

def monoOf (t : Core.Expression.Ty) : Except String LMonoTy :=
  match LTy.toMonoType? (t : LTy) with
  | some m => .ok m
  | none => .error s!"polymorphic type {Std.format (t : LTy)} in Cortex"

def isRefElem (prog : UnorderedProgram) : LMonoTy → Bool
  | .tcons n [] => n.startsWith "$Any" || n == LowerComposites.compositeTy || (prog.findComposite? n).isSome
  | t => (arrayElem? t).isSome

def stuckBool : Expr := mkCall "Int.Le" [stuckInt, intLit 0]

/-- `r` refers to an object: `alloc` gives an object a non-negative address, and a reference to
no object has address -1 (`defaultOf`). -/
def live (r : Expr) : Expr := mkCall "Int.Le" [intLit 0, addr r]

def inBounds (o idx : Expr) : Expr :=
  mkCall "Bool.And" [mkCall "Int.Le" [intLit 0, idx], mkCall "Int.Lt" [idx, objLen o]]

def initialFields (i : Info) (ty : LMonoTy) : Except String Expr :=
  (objectFields i.prog ty).foldrM (init := fNil) fun (r, t) acc => do
    let rt ← runtimeTy i.prog t
    let v := match defaultOf i.prog t with
      | .ok d => box rt d
      | .error _ => stuckBox
    return mkCall "$FCons" [i.fieldOf r, v, acc]

def lowerCmd (i : Info) : IRCmd → Except String (List IRCmd)
  | .new x c md => do
    return alloc i x c (← initialFields i (tcon c)) (intLit (-1)) md
  | .readField x o f md => do
    let t ← match i.prog.findField? f with
      | some d => runtimeTy i.prog d.ty
      | none => throw s!"unknown field {f.owner}.{f.field}"
    return [setTo x (unbox t (fieldGet (objFields (heapGet heap (addr o))) (i.fieldOf f))) md]
  | .writeField o f v md => do
    let t ← match i.prog.findField? f with
      | some d => runtimeTy i.prog d.ty
      | none => throw s!"unknown field {f.owner}.{f.field}"
    let obj := heapGet heap (addr o)
    return [setTo (ident heapVar)
      (heapPut heap (addr o) (mkObj (objTag obj) (fieldSet (objFields obj) (i.fieldOf f) (box t v)) (objLen obj))) md]
  | .newArray x ety len md => do
    let et ← monoOf ety
    let fs ← initialFields i (arrayTy et)
    let okLen := match elemDefault i.prog ety with
      | .ok _ => mkCall "Int.Le" [intLit 0, len]
      | .error _ => stuckBool
    return alloc i x (LowerComposites.arrayTag (arrayTy et)) fs (ite okLen len stuckInt) md
  | .readElem x arr idx t md => do
    let rt ← runtimeTy i.prog t
    let obj := heapGet heap (addr arr)
    let d ← elemDefault i.prog t
    let tagOk := tagIn (LowerComposites.typeTagOf arr) (arraysBelow i (arrayTy (← monoOf t)))
    let ok := mkCall "Bool.And" [tagOk, inBounds obj idx]
    return [setTo x (unbox rt (ite ok (elemGet (objFields obj) (elemKey idx) (box rt d)) stuckBox)) md]
  | .writeElem arr idx v t md => do
    let rt ← runtimeTy i.prog t
    let _ ← elemDefault i.prog t
    let obj := heapGet heap (addr arr)
    let tagOk := tagIn (LowerComposites.typeTagOf arr) (arraysBelow i (arrayTy (← monoOf t)))
    let ok := mkCall "Bool.And" [tagOk, inBounds obj idx]
    return [setTo (ident heapVar)
      (heapPut heap (addr arr) (mkObj (objTag obj)
        (ite ok (fieldPut (objFields obj) (elemKey idx) (box rt v)) stuckFields) (objLen obj))) md]
  | .instanceOf x o t md => do
    let t' ← monoOf t
    if !isRefElem i.prog (valueTy i.prog.constrained t') then return [.instanceOf x o t md]
    let test? := if (arrayElem? t').isSome
      then some (tagIn (LowerComposites.typeTagOf o) (arraysBelow i t'))
      else conTyName? t >>= fun n => pred i.prog.constrained n o
    let some test := test? | return [.instanceOf x o t md]
    return [setTo x (ite (live o) test stuckBool) md]
  | .instanceOfComponent x obj arr md =>
    let tagArr := LowerComposites.typeTagOf arr
    let tagObj := LowerComposites.typeTagOf obj
    let refArrays := i.arrays.filterMap fun a => match arrayElem? a with
      | some e => if isRefElem i.prog e then some (a, e) else none
      | none => none
    let test := refArrays.foldr (init := ff) fun (a, e) acc =>
      ite (eq tagArr (LowerComposites.tagOf (LowerComposites.arrayTag a)))
        (tagIn tagObj (tagsBelow i e)) acc
    let isRef := tagIn tagArr (refArrays.map fun (a, _) => LowerComposites.arrayTag a)
    return [setTo x (ite (mkCall "Bool.And" [live arr, live obj]) (ite isRef test stuckBool) stuckBool) md]
  | .arrayLength x arr md =>
    let obj := heapGet heap (addr arr)
    return [setTo x (ite (mkCall "Int.Le" [intLit 0, objLen obj]) (objLen obj) stuckInt) md]
  | .virtualCall .. => throw "Cortex `virtualCall` must be lowered by LowerDispatch before LowerHeapExec"
  | c => return [c]

def elemCmdTys (prog : UnorderedProgram) : List Core.Expression.Ty :=
  prog.procedures.flatMap fun pr =>
    (pr.body.map (·.cfg.blocks.flatMap (·.2.cmds.filterMap fun
      | .newArray _ t _ _ | .readElem _ _ _ t _ | .writeElem _ _ _ t _ => some t
      | _ => none))).getD []

def boxTypes (prog : UnorderedProgram) (arrays : List LMonoTy) : Except String (List LMonoTy) := do
  let fieldTys ← prog.composites.flatMap (·.fields) |>.mapM fun f => runtimeTy prog f.ty
  let elems := (elemCmdTys prog ++ arrays.filterMap fun a => (arrayElem? a).map mono).filter fun t =>
    (elemDefault prog t).toOption.isSome
  let elemTys ← elems.mapM (runtimeTy prog)
  return (fieldTys ++ elemTys).foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []

def info (prog : UnorderedProgram) : Info :=
  let arrays := LowerComposites.arrayTypes prog
  { prog, arrays, tags := prog.composites.map (·.name) ++ arrays.map LowerComposites.arrayTag,
    fields := prog.composites.flatMap fun c => c.fields.map fun f => ⟨c.name, f.name⟩ }

def run (prog : UnorderedProgram) : Except String UnorderedProgram := do
  let info := info prog
  if prog.composites.isEmpty && info.arrays.isEmpty then return prog
  let tys ← boxTypes prog info.arrays
  let procedures ← prog.procedures.mapM fun p => do
    match p.body with
    | none => return p
    | some b =>
      let blocks ← b.cfg.blocks.mapM fun (l, blk) => do
        let cmds ← blk.cmds.flatMapM (lowerCmd info)
        return (l, { blk with cmds })
      return { p with body := some { b with cfg := { b.cfg with blocks } } }
  return { prog with
    procedures
    datatypes := prog.datatypes ++ datatypes tys
    functions := prog.functions ++ functions
    globals := (ident heapVar, mono (tcon heapTy)) :: (ident nextVar, mono .int) :: prog.globals
    globalInit := .init (ident heapVar) (mono (tcon heapTy)) (.det hNil) .empty ::
      .init (ident nextVar) (mono .int) (.det (intLit 0)) .empty :: prog.globalInit }

partial def eraseArrayTys : LMonoTy → LMonoTy
  | .tcons "Array" [_] => tcon LowerComposites.compositeTy
  | .tcons n args => .tcons n (args.map eraseArrayTys)
  | t => t

def eraseArrays (p : UnorderedProgram) : UnorderedProgram := p.mapMonoTys eraseArrayTys

def pass : Pass := Pass.onUnordered "LowerHeapExec" run

end

end Cortex.LowerHeapExec
