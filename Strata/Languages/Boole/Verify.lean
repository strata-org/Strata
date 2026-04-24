/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Boole.Boole
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Verifier
public import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprWF
public import Strata.DL.Imperative.Stmt

public section

namespace Strata.Boole

open Lambda

/--
Boole verification pipeline:

`Strata.Program` -> `BooleDDM.Program.ofAst` -> `BooleDDM.Program`
-> `toCoreProgram` -> `Core.Program` -> `Core.verify`
-/

structure TranslateState where
  fileName : String := ""
  gctx : GlobalContext := {}
  fvarIsOp : Array Bool := #[]
  tyBVars : Array String := #[]
  bvars : Array Core.Expression.Expr := #[]
  labelCounter : Nat := 0
  globalVarCounter : Nat := 0
  /-- Maps procedure names to their modifies variables with types,
      collected in a pre-pass so call sites can add extra args/lhs. -/
  modifiesMap : Std.HashMap String (List (Core.Expression.Ident × Lambda.LMonoTy)) := {}
  /-- Names of in-out parameters for the current procedure being translated.
      `old x` is only applied to these variables; for others `old x = x`. -/
  currentInoutNames : List String := []
  /-- Types of global variables, collected in a pre-pass.
      Used to add globals as input parameters to procedures. -/
  globalVarTypes : Std.HashMap String Lambda.LMonoTy := {}

abbrev TranslateM := StateT TranslateState (Except DiagnosticModel)

private def mkIdent (name : String) : Core.Expression.Ident :=
  ⟨name, ()⟩

def topLevelBlockProcedureName : String := "__Boole_top"

private def throwAt (m : SourceRange) (msg : String) : TranslateM α := do
  throw (.withRange ⟨⟨(← get).fileName⟩, m⟩ msg)

private def defaultLabel (m : SourceRange) (pfx : String) (l? : Option (BooleDDM.Label SourceRange)) : TranslateM String := do
  match l? with
  | some (.label _ ⟨_, l⟩) => return l
  | none =>
    let i := (← get).labelCounter
    modify fun s => { s with labelCounter := i + 1 }
    return s!"{pfx}_{i}_{m.start}"

private def withTypeBVars (xs : List String) (k : TranslateM α) : TranslateM α := do
  let old := (← get).tyBVars
  modify fun s => { s with tyBVars := old ++ xs.toArray }
  try
    let out ← k
    modify fun s => { s with tyBVars := old }
    return out
  catch e =>
    modify fun s => { s with tyBVars := old }
    throw e

private def withBVars (xs : List String) (k : TranslateM α) : TranslateM α := do
  let old := (← get).bvars
  let fresh := xs.toArray.map (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr))
  modify fun s => { s with bvars := old ++ fresh }
  try
    let out ← k
    modify fun s => { s with bvars := old }
    return out
  catch e =>
    modify fun s => { s with bvars := old }
    throw e

private def withBVarExprs (xs : Array Core.Expression.Expr) (k : TranslateM α) : TranslateM α := do
  let old := (← get).bvars
  modify fun s => { s with bvars := old ++ xs }
  try
    let out ← k
    modify fun s => { s with bvars := old }
    return out
  catch e =>
    modify fun s => { s with bvars := old }
    throw e

private def getTypeBVarName (m : SourceRange) (i : Nat) : TranslateM String := do
  let xs := (← get).tyBVars
  if i < xs.size then
    match xs[(xs.size - i - 1)]? with
    | some n => return n
    | none => throwAt m s!"Unknown bound type variable with index {i}"
  else
    throwAt m s!"Unknown bound type variable with index {i}"

private def getFVarName (m : SourceRange) (i : Nat) : TranslateM String := do
  match (← get).gctx.nameOf? i with
  | some n => return n
  | none => throwAt m s!"Unknown free variable with index {i}"

private def getFVarIsOp (m : SourceRange) (i : Nat) : TranslateM Bool := do
  let st ← get
  match st.fvarIsOp[i]? with
  | some b => return b
  | none =>
    match st.gctx.vars[i]? with
    | some (_, .expr _) => return true
    | some (_, .type _ _) => return false
    | none => throwAt m s!"Unknown free variable with index {i}"

private def getBVarExpr (m : SourceRange) (i : Nat) : TranslateM Core.Expression.Expr := do
  let xs := (← get).bvars
  if i < xs.size then
    match xs[(xs.size - i - 1)]? with
    | some (.bvar _ _) => return (.bvar () i)
    | some e => return e
    | none => throwAt m s!"Unknown bound variable with index {i}"
  else
    throwAt m s!"Unknown bound variable with index {i}"

private def typeArgsToList : BooleDDM.TypeArgs SourceRange → List String
  | .type_args _ ⟨_, xs⟩ =>
    xs.toList.map fun
      | .type_var _ ⟨_, n⟩ => n

private def bindingsToList : BooleDDM.Bindings SourceRange → List (BooleDDM.Binding SourceRange)
  | .mkBindings _ ⟨_, xs⟩ => xs.toList

private def declListToListRev : BooleDDM.DeclList SourceRange → List (BooleDDM.Bind SourceRange) → List (BooleDDM.Bind SourceRange)
  | .declAtom _ b, acc => b :: acc
  | .declPush _ bs b, acc => declListToListRev bs (b :: acc)

private def declListToList : BooleDDM.DeclList SourceRange → List (BooleDDM.Bind SourceRange)
  | ds => declListToListRev ds []

private def monoDeclListToListRev : BooleDDM.MonoDeclList SourceRange → List (BooleDDM.MonoBind SourceRange) → List (BooleDDM.MonoBind SourceRange)
  | .monoDeclAtom _ b, acc => b :: acc
  | .monoDeclPush _ bs b, acc => monoDeclListToListRev bs (b :: acc)

private def monoDeclListToList : BooleDDM.MonoDeclList SourceRange → List (BooleDDM.MonoBind SourceRange)
  | ds => monoDeclListToListRev ds []

private def constructorListToListRev : BooleDDM.ConstructorList SourceRange → List (BooleDDM.Constructor SourceRange) → List (BooleDDM.Constructor SourceRange)
  | .constructorListAtom _ c, acc => c :: acc
  | .constructorListPush _ cs c, acc => constructorListToListRev cs (c :: acc)

private def constructorListToList : BooleDDM.ConstructorList SourceRange → List (BooleDDM.Constructor SourceRange)
  | cs => constructorListToListRev cs []

private def toCoreMetaData (sr : SourceRange) : TranslateM (Imperative.MetaData Core.Expression) := do
  let file := (← get).fileName
  let uri : Uri := .file file
  let fileRangeElt := ⟨Imperative.MetaData.fileRange, .fileRange ⟨uri, sr⟩⟩
  return #[fileRangeElt]

private def mkCoreApp (op : Core.Expression.Expr) (args : List Core.Expression.Expr) : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () op args

private def typeRange : Boole.Type → SourceRange
  | .bvar m _ => m
  | .tvar m _ => m
  | .fvar m _ _ => m
  | .arrow m _ _ => m
  | .bool m => m
  | .int m => m
  | .real m => m
  | .string m => m
  | .regex m => m
  | .bv1 m => m
  | .bv8 m => m
  | .bv16 m => m
  | .bv32 m => m
  | .bv64 m => m
  | .Map m _ _ => m
  | .Sequence m _ => m

def toCoreMonoType (t : Boole.Type) : TranslateM Lambda.LMonoTy := do
  match t with
  | .bvar m n => return .ftvar (← getTypeBVarName m n)
  | .tvar _ n => return .ftvar n
  | .fvar m i args => return .tcons (← getFVarName m i) (← args.mapM toCoreMonoType).toList
  | .arrow _ a b => return .arrow (← toCoreMonoType a) (← toCoreMonoType b)
  | .bool _ => return .bool
  | .int _ => return .int
  | .string _ => return .string
  | .bv1 _ => return .bitvec 1
  | .bv8 _ => return .bitvec 8
  | .bv16 _ => return .bitvec 16
  | .bv32 _ => return .bitvec 32
  | .bv64 _ => return .bitvec 64
  | .Map _ v k => return .tcons "Map" [← toCoreMonoType k, ← toCoreMonoType v]
  | _ => throwAt (typeRange t) s!"Unsupported Boole type: {repr t}"

def toCoreType (t : Boole.Type) : TranslateM Core.Expression.Ty := do
  return .forAll [] (← toCoreMonoType t)

private def toCoreBinding (b : BooleDDM.Binding SourceRange) : TranslateM (Core.Expression.Ident × Lambda.LMonoTy) := do
  match b with
  | .mkBinding _ ⟨_, n⟩ tp | .outBinding _ ⟨_, n⟩ tp
  | .inoutBinding _ ⟨_, n⟩ tp | .casesBinding _ ⟨_, n⟩ tp =>
    match tp with
    | .expr ty => return (mkIdent n, ← toCoreMonoType ty)
    | .type m => throwAt m "Unexpected Type parameter in term binding"

private def bindingName : BooleDDM.Binding SourceRange → String
  | .mkBinding _ ⟨_, n⟩ _ | .outBinding _ ⟨_, n⟩ _
  | .inoutBinding _ ⟨_, n⟩ _ | .casesBinding _ ⟨_, n⟩ _ => n

private def hasOutOrInoutBinding (bs : BooleDDM.Bindings SourceRange) : Option (String × String) :=
  (bindingsToList bs).findSome? fun b =>
    match b with
    | .outBinding _ ⟨_, n⟩ _ => some (n, "out")
    | .inoutBinding _ ⟨_, n⟩ _ => some (n, "inout")
    | _ => none

private def toCoreBind (b : BooleDDM.Bind SourceRange) : TranslateM (Core.Expression.Ident × Core.Expression.Ty) := do
  match b with
  | .bind_mk _ ⟨_, n⟩ _ ty => return (mkIdent n, ← toCoreType ty)

private def toCoreMonoBind (b : BooleDDM.MonoBind SourceRange) : TranslateM (Core.Expression.Ident × Lambda.LMonoTy) := do
  match b with
  | .mono_bind_mk _ ⟨_, n⟩ ty => return (mkIdent n, ← toCoreMonoType ty)

def toCoreTypedUn (m : SourceRange) (ty : Boole.Type) (op : String) (a : Core.Expression.Expr) : TranslateM Core.Expression.Expr := do
  let .int _ := ty
    | throwAt m s!"Unsupported typed operator type: {repr ty}"
  let iop : Core.Expression.Expr := .op () ⟨s!"Int.{op}", ()⟩ none
  return .app () iop a

def toCoreTypedBin (m : SourceRange) (ty : Boole.Type) (op : String) (a b : Core.Expression.Expr) : TranslateM Core.Expression.Expr := do
  let .int _ := ty
    | throwAt m s!"Unsupported typed operator type: {repr ty}"
  let iop : Core.Expression.Expr := .op () ⟨s!"Int.{op}", ()⟩ none
  return mkCoreApp iop [a, b]

private def toCoreExtensionalEq
    (m : SourceRange)
    (ty : Boole.Type)
    (a b : Core.Expression.Expr) : TranslateM Core.Expression.Expr := do
  match ty with
  | .Map _ _ keyTy =>
      let keyTy' ← toCoreMonoType keyTy
      let idx : Core.Expression.Expr := .bvar () 0
      let a := Lambda.LExpr.liftBVars 1 a
      let b := Lambda.LExpr.liftBVars 1 b
      let lhs := mkCoreApp Core.mapSelectOp [a, idx]
      let rhs := mkCoreApp Core.mapSelectOp [b, idx]
      let trigger := lhs
      return .quant () .all "" (some keyTy') trigger (.eq () lhs rhs)
  | _ =>
      throwAt m s!"Extensional equality is currently only supported for Map types, got: {repr ty}"

private def oldifyExpr (inoutNames : List String) : Core.Expression.Expr → Core.Expression.Expr
  | .fvar m ident ty =>
      if Core.CoreIdent.isOldIdent ident then .fvar m ident ty
      else if inoutNames.contains ident.name then .fvar m (Core.CoreIdent.mkOld ident.name) ty
      else .fvar m ident ty
  | .app m f a => .app m (oldifyExpr inoutNames f) (oldifyExpr inoutNames a)
  | .eq m a b => .eq m (oldifyExpr inoutNames a) (oldifyExpr inoutNames b)
  | .ite m c t f => .ite m (oldifyExpr inoutNames c) (oldifyExpr inoutNames t) (oldifyExpr inoutNames f)
  | .quant m k n ty trig body => .quant m k n ty (oldifyExpr inoutNames trig) (oldifyExpr inoutNames body)
  | .abs m n ty body => .abs m n ty (oldifyExpr inoutNames body)
  | e => e

mutual

def toCoreQuant
    (isForall : Bool)
    (ds : BooleDDM.DeclList SourceRange)
    (body : Boole.Expr) : TranslateM Core.Expression.Expr := do
  let decls := declListToList ds
  let tys ← decls.mapM fun (.bind_mk _ _ _ ty) => toCoreMonoType ty
  let qBVars : Array Core.Expression.Expr := (decls.toArray.mapIdx fun i _ => .bvar () i)
  let body' ← withBVarExprs qBVars (toCoreExpr body)
  let q := if isForall then Lambda.QuantifierKind.all else Lambda.QuantifierKind.exist
  return tys.foldr (fun ty acc => .quant () q "" (some ty) (.bvar () 0) acc) body'

/--
Normalize Boole quantifier surface-syntax variants to a single lowering path.

The DDM grammar accepts both ASCII (`forall`, `exists`) and Unicode (`∀`, `∃`)
spellings, with and without trigger lists. The generated Boole AST keeps those
spellings as distinct constructors, so the frontend merges them here before
lowering into Core. Legacy dotted Unicode separators are normalized earlier in
`Strata.DDM.Elab`, so this helper only needs to collapse the remaining AST
constructor variants.
-/
private def toCoreQuantExpr? (e : Boole.Expr) : Option (TranslateM Core.Expression.Expr) :=
  match e with
  | .forall _ ds body
  | .forall_unicode _ ds body
  | .forallT _ ds _ body
  | .forall_unicodeT _ ds _ body =>
      some (toCoreQuant true ds body)
  | .exists _ ds body
  | .exists_unicode _ ds body
  | .existsT _ ds _ body
  | .exists_unicodeT _ ds _ body =>
      some (toCoreQuant false ds body)
  | _ => none

def toCoreExpr (e : Boole.Expr) : TranslateM Core.Expression.Expr := do
  if let some q := toCoreQuantExpr? e then
    return ← q
  match e with
  | .fvar m i =>
    let id := mkIdent (← getFVarName m i)
    if (← getFVarIsOp m i) then
      return .op () id none
    else
      return .fvar () id none
  | .bvar m i => getBVarExpr m i
  | .app _ f a => return .app () (← toCoreExpr f) (← toCoreExpr a)
  | .not _ a => return .app () Core.boolNotOp (← toCoreExpr a)
  | .bv1Lit _ ⟨_, n⟩ => return .bitvecConst () 1 n
  | .bv8Lit _ ⟨_, n⟩ => return .bitvecConst () 8 n
  | .bv16Lit _ ⟨_, n⟩ => return .bitvecConst () 16 n
  | .bv32Lit _ ⟨_, n⟩ => return .bitvecConst () 32 n
  | .bv64Lit _ ⟨_, n⟩ => return .bitvecConst () 64 n
  | .natToInt _ ⟨_, n⟩ => return .intConst () (Int.ofNat n)
  | .if _ _ c t f => return .ite () (← toCoreExpr c) (← toCoreExpr t) (← toCoreExpr f)
  | .map_get _ _ _ a i => return mkCoreApp Core.mapSelectOp [← toCoreExpr a, ← toCoreExpr i]
  | .map_set _ _ _ a i v => return mkCoreApp Core.mapUpdateOp [← toCoreExpr a, ← toCoreExpr i, ← toCoreExpr v]
  | .btrue _ => return .true ()
  | .bfalse _ => return .false ()
  | .and _ a b => return mkCoreApp Core.boolAndOp [← toCoreExpr a, ← toCoreExpr b]
  | .or _ a b => return mkCoreApp Core.boolOrOp [← toCoreExpr a, ← toCoreExpr b]
  | .equiv _ a b => return mkCoreApp Core.boolEquivOp [← toCoreExpr a, ← toCoreExpr b]
  | .implies _ a b => return mkCoreApp Core.boolImpliesOp [← toCoreExpr a, ← toCoreExpr b]
  | .ext_equal m ty a b => return ← toCoreExtensionalEq m ty (← toCoreExpr a) (← toCoreExpr b)
  | .equal _ _ a b => return .eq () (← toCoreExpr a) (← toCoreExpr b)
  | .not_equal _ _ a b => return .app () Core.boolNotOp (.eq () (← toCoreExpr a) (← toCoreExpr b))
  | .le m ty a b => toCoreTypedBin m ty "Le" (← toCoreExpr a) (← toCoreExpr b)
  | .lt m ty a b => toCoreTypedBin m ty "Lt" (← toCoreExpr a) (← toCoreExpr b)
  | .ge m ty a b => toCoreTypedBin m ty "Ge" (← toCoreExpr a) (← toCoreExpr b)
  | .gt m ty a b => toCoreTypedBin m ty "Gt" (← toCoreExpr a) (← toCoreExpr b)
  | .neg_expr m ty a => toCoreTypedUn m ty "Neg" (← toCoreExpr a)
  | .add_expr m ty a b => toCoreTypedBin m ty "Add" (← toCoreExpr a) (← toCoreExpr b)
  | .sub_expr m ty a b => toCoreTypedBin m ty "Sub" (← toCoreExpr a) (← toCoreExpr b)
  | .mul_expr m ty a b => toCoreTypedBin m ty "Mul" (← toCoreExpr a) (← toCoreExpr b)
  | .div_expr m ty a b => toCoreTypedBin m ty "Div" (← toCoreExpr a) (← toCoreExpr b)
  | .mod_expr m ty a b => toCoreTypedBin m ty "Mod" (← toCoreExpr a) (← toCoreExpr b)
  | .old _ _ a =>
      return oldifyExpr (← get).currentInoutNames (← toCoreExpr a)
  | _ => throw (.fromMessage s!"Unsupported expression: {repr e}")

end

def nestMapSet (base : Core.Expression.Expr) (idxs : List Core.Expression.Expr) (rhs : Core.Expression.Expr) : Core.Expression.Expr :=
  match idxs with
  | [] => rhs
  | [i] => mkCoreApp Core.mapUpdateOp [base, i, rhs]
  | i :: rest =>
    let innerMap := mkCoreApp Core.mapSelectOp [base, i]
    let updatedInner := nestMapSet innerMap rest rhs
    mkCoreApp Core.mapUpdateOp [base, i, updatedInner]

def toCoreInvariants (is : BooleDDM.Invariants SourceRange) :
    TranslateM (List (String × Core.Expression.Expr)) := do
  match is with
  | .nilInvariants _ => return []
  | .consInvariants _ lbl? e rest => do
    let lbl := match lbl?.val with
      | some (.label _ ⟨_, l⟩) => l
      | none => ""
    let e' ← toCoreExpr e
    return (lbl, e') :: (← toCoreInvariants rest)

def lowerFor
    (m : SourceRange)
    (id : Core.Expression.Ident)
    (ty : Lambda.LMonoTy)
    (initExpr guardExpr stepExpr : Core.Expression.Expr)
    (invs : List (String × Core.Expression.Expr))
    (body : List Core.Statement) : TranslateM Core.Statement := do
  let blockLabel ← defaultLabel m "for" none
  let initStmt : Core.Statement := Core.Statement.init id (.forAll [] ty) (.det initExpr) (← toCoreMetaData m)
  let stepStmt : Core.Statement := Core.Statement.set id stepExpr (← toCoreMetaData m)
  let loopBody := body ++ [stepStmt]
  return .block blockLabel [initStmt, .loop (.det guardExpr) none invs loopBody (← toCoreMetaData m)] (← toCoreMetaData m)

private def lowerVarStatement (m : SourceRange) (ds : BooleDDM.DeclList SourceRange) : TranslateM (List Core.Statement) := do
  let mut outRev : List Core.Statement := []
  let mut newBVarsRev : List Core.Expression.Expr := []
  for d in declListToList ds do
    let (id, ty) ← toCoreBind d
    let n := (← get).globalVarCounter
    modify fun st => { st with globalVarCounter := n + 1 }
    let initName := mkIdent s!"init_{id.name}_{n}"
    newBVarsRev := (.fvar () id none : Core.Expression.Expr) :: newBVarsRev
    outRev := Core.Statement.init id ty (.det (.fvar () initName none)) (← toCoreMetaData m) :: outRev
  modify fun st => { st with bvars := st.bvars ++ newBVarsRev.reverse.toArray }
  return outRev.reverse

mutual

def toCoreBlock (b : BooleDDM.Block SourceRange) : TranslateM (List Core.Statement) := do
  match b with
  | .block _ ⟨_, ss⟩ =>
    let parts ← ss.toList.mapM fun s =>
      match s with
      | .varStatement m ds => lowerVarStatement m ds
      | _ => return [← toCoreStmt s]
    return parts.flatten
  termination_by SizeOf.sizeOf b
  decreasing_by simp_all; term_by_mem

/-- Compute the sorted typed-parameter prefix that both procedure headers and
    call sites must agree on.  Returns `(modifiesTyped, readOnlyGlobals)`, each
    sorted by name for deterministic ordering across HashMap iterations. -/
private def getGlobalParamPrefix (n : String)
    : TranslateM (ListMap Core.CoreIdent Lambda.LMonoTy × ListMap Core.CoreIdent Lambda.LMonoTy) := do
  let modifiesTyped : ListMap Core.CoreIdent Lambda.LMonoTy :=
    ((← get).modifiesMap.getD n []).mergeSort (·.1.name < ·.1.name)
  let modifiesNames := modifiesTyped.map (·.fst.name)
  let readOnlyGlobals : ListMap Core.CoreIdent Lambda.LMonoTy :=
    ((← get).globalVarTypes.toList.filterMap fun (name, ty) =>
      if modifiesNames.contains name then none
      else some (mkIdent name, ty)).mergeSort (·.1.name < ·.1.name)
  return (modifiesTyped, readOnlyGlobals)

/-- Build `CallArg` prefix for a call site from `getGlobalParamPrefix`.
    Modified globals become `inoutArg`; read-only globals become `inArg`. -/
private def constructProcArgsPrefix (n : String)
    : TranslateM (List (Core.CallArg Core.Expression)) := do
  let (modifiesTyped, readOnlyGlobals) ← getGlobalParamPrefix n
  let modifiesArgs := modifiesTyped.map fun (id, _) => Core.CallArg.inoutArg id
  let readOnlyArgs := readOnlyGlobals.map
    fun (id, _) => Core.CallArg.inArg (Lambda.LExpr.fvar () id none : Core.Expression.Expr)
  return modifiesArgs ++ readOnlyArgs

def toCoreStmt (s : BooleDDM.Statement SourceRange) : TranslateM Core.Statement := do
  match s with
  | .varStatement m ds =>
    let out ← lowerVarStatement m ds
    let some first := out.head?
      | throwAt m "Empty var declaration list"
    match ds with
    | .declAtom _ _ => return first
    | _ => return .block "var" out (← toCoreMetaData m)
  | .initStatement m ty ⟨_, n⟩ e =>
    let rhs ← toCoreExpr e
    modify fun st => { st with bvars := st.bvars.push (.fvar () (mkIdent n) none) }
    return Core.Statement.init (mkIdent n) (← toCoreType ty) (.det rhs) (← toCoreMetaData m)
  | .assign m _ lhs rhs =>
    let rec lhsParts (lhs : BooleDDM.Lhs SourceRange) : TranslateM (String × List Core.Expression.Expr) := do
      match lhs with
      | .lhsIdent _ ⟨_, n⟩ => return (n, [])
      | .lhsArray _ _ l i =>
        let (n, isRev) ← lhsParts l
        return (n, (← toCoreExpr i) :: isRev)
    let (n, idxsRev) ← lhsParts lhs
    let idxs := idxsRev.reverse
    let base := .fvar () (mkIdent n) none
    return Core.Statement.set (mkIdent n) (nestMapSet base idxs (← toCoreExpr rhs)) (← toCoreMetaData m)
  | .assume m ⟨_, l?⟩ e =>
    return Core.Statement.assume (← defaultLabel m "assume" l?) (← toCoreExpr e) (← toCoreMetaData m)
  | .assert m rc? ⟨_, l?⟩ e =>
    let md ← toCoreMetaData m
    let md := if rc? matches ⟨_, some _⟩ then md.pushElem Imperative.MetaData.reachCheck (.switch true) else md
    return Core.Statement.assert (← defaultLabel m "assert" l?) (← toCoreExpr e) md
  | .cover m rc? ⟨_, l?⟩ e =>
    let md ← toCoreMetaData m
    let md := if rc? matches ⟨_, some _⟩ then md.pushElem Imperative.MetaData.reachCheck (.switch true) else md
    return Core.Statement.cover (← defaultLabel m "cover" l?) (← toCoreExpr e) md
  | .if_statement m c t e =>
    let thenb ← withBVars [] (toCoreBlock t)
    let elseb ← withBVars [] <| match e with
      | .else0 _ => pure []
      | .else1 _ b => toCoreBlock b
    let cond ← match c with
      | .condDet _ expr => pure (.det (← toCoreExpr expr))
      | .condNondet _ => pure .nondet
    return .ite cond thenb elseb (← toCoreMetaData m)
  | .havoc_statement m ⟨_, n⟩ =>
    return Core.Statement.havoc (mkIdent n) (← toCoreMetaData m)
  | .while_statement m g _ invs b =>
    let guard ← match g with
      | .condDet _ expr => pure (.det (← toCoreExpr expr))
      | .condNondet _ => pure .nondet
    return .loop guard none (← toCoreInvariants invs) (← withBVars [] (toCoreBlock b)) (← toCoreMetaData m)
  | .boole_call_statement m ⟨_, lhs⟩ ⟨_, n⟩ ⟨_, args⟩ => do
    let globalsPrefix ← constructProcArgsPrefix n
    let userIn := (← args.toList.mapM toCoreExpr).map Core.CallArg.inArg
    let userOut := (lhs.toList.map (mkIdent ·.val)).map Core.CallArg.outArg
    return Core.Statement.call n (globalsPrefix ++ userIn ++ userOut) (← toCoreMetaData m)
  | .call_statement m ⟨_, n⟩ ⟨_, callArgs⟩ => do
    -- Reject Core-only out/inout call argument syntax in Boole.
    -- Boole uses `call lhs := f(args)` for calls with outputs.
    for ca in callArgs.toList do
      match ca with
      | .callArgOut _ ⟨_, v⟩ =>
        throwAt m s!"'out' argument '{v}' in call to '{n}' is not supported in Boole. Use 'call {v} := {n}(...)' syntax instead."
      | .callArgInout _ ⟨_, v⟩ =>
        throwAt m s!"'inout' argument '{v}' in call to '{n}' is not supported in Boole. Use 'modifies' clauses for mutable globals instead."
      | _ => pure ()
    let globalsPrefix ← constructProcArgsPrefix n
    let userIn ← callArgs.toList.filterMapM fun ca =>
      match ca with
      | .callArgExpr _ e => return some (Core.CallArg.inArg (← toCoreExpr e))
      | _ => return none  -- unreachable: out/inout rejected above
    return Core.Statement.call n (globalsPrefix ++ userIn) (← toCoreMetaData m)
  | .block_statement m ⟨_, l⟩ b =>
    return .block l (← withBVars [] (toCoreBlock b)) (← toCoreMetaData m)
  | .exit_statement m ⟨_, l⟩ =>
    return .exit l (← toCoreMetaData m)
  | .exit_unlabeled_statement m =>
    return .exit none (← toCoreMetaData m)
  | .typeDecl_statement m ⟨_, n⟩ ⟨_, args?⟩ =>
    let params := match args? with
      | none => []
      | some bs => (bindingsToList bs).map bindingName
    return Core.Statement.typeDecl { name := n, params := params } (← toCoreMetaData m)
  | .funcDecl_statement m ⟨_, n⟩ ⟨_, targs?⟩ bs ret ⟨_, pres⟩ body ⟨_, inline?⟩ =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      let bsList := bindingsToList bs
      let inputsMono ← bsList.mapM toCoreBinding
      let outputMono ← toCoreMonoType ret
      let inputs : ListMap Core.Expression.Ident Core.Expression.Ty :=
        inputsMono.map (fun (id, mty) => (id, .forAll [] mty))
      let inputNames := bsList.map bindingName
      let pair ← (withBVars inputNames do
        let mut precondsRev : List (DL.Util.FuncPrecondition Core.Expression.Expr Unit) := []
        for p in pres.toList do
          match p with
          | .requires_spec _ _ _ cond =>
            precondsRev := { expr := ← toCoreExpr cond, md := () } :: precondsRev
          | _ => pure ()
        let bodyExpr ← toCoreExpr body
        return (precondsRev.reverse, bodyExpr) : TranslateM (List (DL.Util.FuncPrecondition Core.Expression.Expr Unit) × Core.Expression.Expr))
      let (preconds, bodyExpr) := pair
      let funcTy := Lambda.LMonoTy.mkArrow outputMono ((inputsMono.map (·.2)).reverse)
      let decl : Imperative.PureFunc Core.Expression := {
        name := mkIdent n
        typeArgs := tys
        inputs := inputs
        output := .forAll [] outputMono
        body := some bodyExpr
        attr := if inline?.isSome then #[.inline] else #[]
        axioms := []
        preconditions := preconds
      }
      -- Keep function name in local scope for subsequent statements.
      modify fun st => { st with bvars := st.bvars.push (.op () (mkIdent n) (some funcTy)) }
      return .funcDecl decl (← toCoreMetaData m)
  | .for_statement m v init guard step invs body =>
    let (id, ty) ← toCoreMonoBind v
    withBVars [id.name] do
      let body ← withBVars [] (toCoreBlock body)
      lowerFor
        m id ty
        (← toCoreExpr init)
        (← toCoreExpr guard)
        (← toCoreExpr step)
        (← toCoreInvariants invs)
        body
  | .for_to_by_statement m v init limit ⟨_, step?⟩ invs body =>
    let (id, ty) ← toCoreMonoBind v
    let limitExpr ← toCoreExpr limit
    withBVars [id.name] do
      let initExpr ← toCoreExpr init
      let guard := mkCoreApp Core.intLeOp [.fvar () id none, limitExpr]
      let stepExpr ← ((match step? with
        | none => pure (.intConst () 1)
        | some (.step _ e) => toCoreExpr e) : TranslateM Core.Expression.Expr)
      let body ← withBVars [] (toCoreBlock body)
      lowerFor
        m id ty
        initExpr
        guard
        (mkCoreApp Core.intAddOp [.fvar () id none, stepExpr])
        (← toCoreInvariants invs)
        body
  | .for_down_to_by_statement m v init limit ⟨_, step?⟩ invs body =>
    let (id, ty) ← toCoreMonoBind v
    let limitExpr ← toCoreExpr limit
    withBVars [id.name] do
      let initExpr ← toCoreExpr init
      let guard := mkCoreApp Core.intLeOp [limitExpr, .fvar () id none]
      let stepExpr ← ((match step? with
        | none => pure (.intConst () 1)
        | some (.step _ e) => toCoreExpr e) : TranslateM Core.Expression.Expr)
      let body ← withBVars [] (toCoreBlock body)
      lowerFor
        m id ty
        initExpr
        guard
        (mkCoreApp Core.intSubOp [.fvar () id none, stepExpr])
        (← toCoreInvariants invs)
        body
  termination_by SizeOf.sizeOf s

end

private def checkAttrOf (f? : Option (BooleDDM.Free SourceRange)) : Core.Procedure.CheckAttr :=
  match f? with
  | some _ => .Free
  | none => .Default

private def toCoreDatatypeConstr
    (dtypeName : String)
    (c : BooleDDM.Constructor SourceRange) : TranslateM (Lambda.LConstr Unit) := do
  match c with
  | .constructor_mk _ ⟨_, cname⟩ ⟨_, fields?⟩ =>
    let args ← ((match fields? with
      | none => pure []
      | some ⟨_, fs⟩ => fs.toList.mapM toCoreBinding) : TranslateM (List (Core.Expression.Ident × Lambda.LMonoTy)))
    return { name := mkIdent cname
             args := args
             testerName := s!"{dtypeName}..is{cname}" }

private def toCoreDatatype
    (m : SourceRange)
    (dtypeName : String)
    (typeParams : List String)
    (ctors : BooleDDM.ConstructorList SourceRange) : TranslateM (Lambda.LDatatype Unit) := do
  let ctorList := constructorListToList ctors
  match ctorList with
  | [] => throwAt m s!"Datatype {dtypeName} must have at least one constructor"
  | ctor :: rest =>
    let first ← toCoreDatatypeConstr dtypeName ctor
    let restConstrs ← rest.mapM (toCoreDatatypeConstr dtypeName)
    let constrs := first :: restConstrs
    return { name := dtypeName
             typeArgs := typeParams
             constrs := constrs
             constrs_ne := by simp }

private def toCoreDatatypeDecl (decl : BooleDDM.DatatypeDecl SourceRange) : TranslateM (Lambda.LDatatype Unit) := do
  match decl with
  | .datatype_decl m ⟨_, dtypeName⟩ ⟨_, typeParams?⟩ ctors =>
    let typeParams := match typeParams? with
      | none => []
      | some bs => (bindingsToList bs).map bindingName
    withTypeBVars typeParams do
      toCoreDatatype m dtypeName typeParams ctors

private def toCoreSpecElts (_m : SourceRange) (pname : String) (elts : Array (BooleDDM.SpecElt SourceRange)) : TranslateM Core.Procedure.Spec := do
  let mut reqs : List (Core.CoreLabel × Core.Procedure.Check) := []
  let mut enss : List (Core.CoreLabel × Core.Procedure.Check) := []
  for e in elts.toList do
    match e with
    | .modifies_spec _ _ => pure ()
    | .requires_spec em ⟨_, l?⟩ ⟨_, free?⟩ cond =>
      let md ← toCoreMetaData em
      reqs := (← defaultLabel em s!"{pname}_requires" l?, { expr := ← toCoreExpr cond, attr := checkAttrOf free?, md := md }) :: reqs
    | .ensures_spec em ⟨_, l?⟩ ⟨_, free?⟩ cond =>
      let md ← toCoreMetaData em
      enss := (← defaultLabel em s!"{pname}_ensures" l?, { expr := ← toCoreExpr cond, attr := checkAttrOf free?, md := md }) :: enss
  return { preconditions := reqs.reverse, postconditions := enss.reverse }

private def toCoreSpec (m : SourceRange) (pname : String) (spec? : Option (BooleDDM.Spec SourceRange)) : TranslateM Core.Procedure.Spec := do
  match spec? with
  | none => return { preconditions := [], postconditions := [] }
  | some (.spec_mk _ ⟨_, elts⟩) =>
    toCoreSpecElts m pname elts

private def lowerPureFuncDef
    (m : SourceRange)
    (n : String)
    (tys : List String)
    (bs : BooleDDM.Bindings SourceRange)
    (ret : Boole.Type)
    (pres : Array (BooleDDM.SpecElt SourceRange))
    (body : Boole.Expr)
    (inline : Bool) : TranslateM Core.Function := do
  withTypeBVars tys do
    let bsList := bindingsToList bs
    let inputs ← bsList.mapM toCoreBinding
    let inputNames := bsList.map bindingName
    let pres ← withBVars inputNames (toCoreSpecElts m n pres)
    let pres := pres.preconditions.map (fun (_, c) => ⟨c.expr, ()⟩)
    let body ← withBVars inputNames (toCoreExpr body)
    return {
      name := mkIdent n
      typeArgs := tys
      inputs := inputs
      output := ← toCoreMonoType ret
      body := some body
      concreteEval := none
      attr := if inline then #[.inline] else #[]
      axioms := []
      preconditions := pres
    }

/--
Classify command-introduced free symbols:
- constant/function declarations are treated as function symbols,
- variable/type/datatype declarations are treated as term/type symbols.
-/
private def registerCommandSymbols (cmd : BooleDDM.Command SourceRange) : List Bool :=
  match cmd with
  | .command_typedecl _ _ _ => [false]
  | .command_typesynonym _ _ _ _ _ => [false]
  | .command_constdecl _ _ _ _ => [true]
  | .command_fndecl _ _ _ _ _ => [true]
  | .command_fndef _ _ _ _ _ _ _ _ => [true]
  | .command_recfndefs _ ⟨_, funcs⟩ => funcs.toList.map (fun _ => true)
  | .command_var _ _ => [false]
  -- Procedure names are referenced by call statements directly and are not Expr.fvar symbols.
  | .boole_procedure _ _ _ _ _ _ _ | .command_procedure _ _ _ _ _ _ => []
  | .command_datatypes _ ⟨_, decls⟩ => decls.toList.map (fun _ => false)
  | .command_block _ _ => []
  | .command_axiom _ _ _ => []
  | .command_distinct _ _ _ => []

/--
Build the symbol-class table used by `getFVarIsOp`.
-/
private def initFVarIsOp (p : Boole.Program) : Array Bool :=
  match p with
  | .prog _ ⟨_, cmds⟩ =>
    (cmds.map registerCommandSymbols).toList.flatten.toArray

private def collectModifiesFromSpec
    (fileName : String)
    (pname : String)
    (spec? : Option (BooleDDM.Spec SourceRange))
    (varTypes : Std.HashMap String Lambda.LMonoTy)
    : Except DiagnosticModel (List (Core.Expression.Ident × Lambda.LMonoTy)) := do
  match spec? with
  | none => return []
  | some (.spec_mk _ ⟨_, elts⟩) =>
    let mut mods : List (Core.Expression.Ident × Lambda.LMonoTy) := []
    for e in elts.toList do
      match e with
      | .modifies_spec m ⟨_, names⟩ =>
        for ⟨_, vname⟩ in names.toList do
          match varTypes.get? vname with
          | some ty => mods := (mkIdent vname, ty) :: mods
          | none =>
            throw (.withRange ⟨⟨fileName⟩, m⟩
              f!"modifies variable '{vname}' in procedure '{pname}' not found in global variable declarations")
      | _ => pure ()
    return mods.reverse

private def translateProcedureDecl
    (m : SourceRange) (n : String) (tys : List String)
    (inputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (spec? : Option (BooleDDM.Spec SourceRange))
    (body? : Option (BooleDDM.Block SourceRange))
    : TranslateM (List Core.Decl) := do
  let (modifiesTyped, readOnlyGlobals) ← getGlobalParamPrefix n
  let allInputs := modifiesTyped ++ readOnlyGlobals ++ inputs
  let allOutputs := modifiesTyped ++ outputs
  -- Only user-declared names need bvar scoping; globals are resolved as fvars.
  let inputNames := inputs.map (·.fst.name)
  let outputNames := outputs.map (·.fst.name)
  -- Set inout names so `old` is only applied to modifies-converted parameters.
  let inoutNames := modifiesTyped.map (·.fst.name)
  let savedInoutNames := (← get).currentInoutNames
  modify fun s => { s with currentInoutNames := inoutNames }
  let spec ← withBVars (inputNames ++ outputNames) (toCoreSpec m n spec?)
  -- Wrap body in a labeled block so `exit procName;` implements early return.
  let bodyStmts ← match body? with
    | none => pure []
    | some b => withBVars (inputNames ++ outputNames) (toCoreBlock b)
  modify fun s => { s with currentInoutNames := savedInoutNames }
  let body : List Core.Statement := match bodyStmts with
    | [] => []
    | stmts => [.block n stmts .empty]
  return [.proc {
    header := { name := mkIdent n, typeArgs := tys, inputs := allInputs, outputs := allOutputs }
    spec := spec
    body := body
  } .empty]

def toCoreDecls (cmd : BooleDDM.Command SourceRange) : TranslateM (List Core.Decl) := do
  match cmd with
  | .boole_procedure m nameAnn targsAnn ins outsAnn specAnn bodyAnn =>
    let n := nameAnn.val
    let tys := match targsAnn.val with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      let inputs ← (bindingsToList ins).mapM toCoreBinding
      let outputs ← match outsAnn.val with
        | none => pure []
        | some os => (monoDeclListToList os).mapM toCoreMonoBind
      translateProcedureDecl m n tys inputs outputs specAnn.val bodyAnn.val
  | .command_procedure m nameAnn targsAnn ins specAnn bodyAnn =>
    let n := nameAnn.val
    if let some (param, kind) := hasOutOrInoutBinding ins then
      throwAt m s!"Boole procedure '{n}': '{kind}' modifier on parameter '{param}' is not supported. Use 'returns' syntax instead, e.g. 'procedure {n}(...) returns ({param} : T)'."
    let tys := match targsAnn.val with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      let inputs ← (bindingsToList ins).mapM toCoreBinding
      translateProcedureDecl m n tys inputs [] specAnn.val bodyAnn.val
  | .command_typedecl _ ⟨_, n⟩ ⟨_, args?⟩ =>
    let params := match args? with
      | none => []
      | some bs => (bindingsToList bs).map bindingName
    return [.type (.con { name := n, params := params }) .empty]
  | .command_typesynonym _ ⟨_, n⟩ ⟨_, args?⟩ _ rhs =>
    let tys := match args? with
      | none => []
      | some bs => (bindingsToList bs).map bindingName
    withTypeBVars tys do
      return [.type (.syn { name := n, typeArgs := tys, type := ← toCoreMonoType rhs }) .empty]
  | .command_constdecl _ ⟨_, n⟩ ⟨_, targs?⟩ ret =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      return [.func { name := mkIdent n, typeArgs := tys, inputs := [], output := ← toCoreMonoType ret, body := none, concreteEval := none, attr := #[], axioms := [] } .empty]
  | .command_fndecl _ ⟨_, n⟩ ⟨_, targs?⟩ bs ret =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      return [
        .func { name := mkIdent n, typeArgs := tys, inputs := ← (bindingsToList bs).mapM toCoreBinding, output := ← toCoreMonoType ret, body := none, concreteEval := none, attr := #[], axioms := [] }
           .empty]
  | .command_fndef m ⟨_, n⟩ ⟨_, targs?⟩ bs ret ⟨_, pres⟩ body ⟨_, inline?⟩ =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    return [.func (← lowerPureFuncDef m n tys bs ret pres body inline?.isSome) .empty]
  | .command_recfndefs _ ⟨_, funcs⟩ =>
    let fs ← funcs.toList.mapM fun
      | .recfn_decl m ⟨_, n⟩ ⟨_, targs?⟩ bs ret ⟨_, pres⟩ body => do
        let tys := match targs? with | none => [] | some ts => typeArgsToList ts
        let f ← lowerPureFuncDef m n tys bs ret pres body false
        return { f with isRecursive := true }
    return [.recFuncBlock fs .empty]
  | .command_var _m _b =>
    return []
  | .command_axiom m ⟨_, l?⟩ e =>
    return [.ax { name := ← defaultLabel m "axiom" l?, e := ← toCoreExpr e } .empty]
  | .command_distinct m ⟨_, l?⟩ ⟨_, es⟩ =>
    return [.distinct (mkIdent (← defaultLabel m "distinct" l?)) (← es.toList.mapM toCoreExpr) .empty]
  | .command_block _ b =>
    -- Core decls do not have a standalone "top-level block" form, so a Boole
    -- command-level block is wrapped as a synthetic procedure declaration.
    return [.proc {
      header := { name := mkIdent topLevelBlockProcedureName, typeArgs := [], inputs := [], outputs := [] }
      spec := { preconditions := [], postconditions := [] }
      body := ← toCoreBlock b
    } .empty]
  | .command_datatypes _ ⟨_, decls⟩ =>
    return [.type (.data (← decls.toList.mapM toCoreDatatypeDecl)) .empty]

/-- Render a `Boole.Program` to a format object using the provided `GlobalContext` and
`DialectMap`. These should come from the originating `Strata.Program` (i.e. `env.globalContext`
and `env.dialects`), since fvar indices in `prog` are relative to that context.

This mirrors `Core.formatProgram`: both functions accept an external context rather than
recomputing one from the program structure, because the container operation (`Boole.prog`)
carries no binding specs and therefore produces an empty `GlobalContext` when processed alone.
-/
def formatProgram (prog : Boole.Program) (gctx : GlobalContext) (dialects : DialectMap) : Std.Format :=
  let ctx := FormatContext.ofDialects dialects gctx {}
  let state : FormatState := {
    openDialects := dialects.toList.foldl (init := {}) fun a d => a.insert d.name
  }
  (mformat (ArgF.op prog.toAst) ctx state).format

def toCoreProgram (p : Boole.Program) (gctx : GlobalContext := {}) (fileName : String := "") : Except DiagnosticModel Core.Program := do
  match p with
  | .prog _ ⟨_, cmds⟩ =>
    let fvarIsOp := initFVarIsOp p
    -- Pre-pass: collect global variable types and modifies info per procedure.
    let mut varTypes : Std.HashMap String Lambda.LMonoTy := {}
    let mut modMap : Std.HashMap String (List (Core.Expression.Ident × Lambda.LMonoTy)) := {}
    for cmd in cmds do
      match cmd with
      | .command_var _ b =>
        match b with
        | .bind_mk _ ⟨_, n⟩ _ ty =>
          match (toCoreMonoType ty).run' { gctx := gctx, fvarIsOp := fvarIsOp } with
          | .ok mty => varTypes := varTypes.insert n mty
          | .error _ => pure ()
      | .boole_procedure _ nameAnn _ _ _ specAnn _ =>
        let mods ← collectModifiesFromSpec fileName nameAnn.val specAnn.val varTypes
        if !mods.isEmpty then modMap := modMap.insert nameAnn.val mods
      | .command_procedure _ nameAnn _ _ specAnn _ =>
        let mods ← collectModifiesFromSpec fileName nameAnn.val specAnn.val varTypes
        if !mods.isEmpty then modMap := modMap.insert nameAnn.val mods
      | _ => pure ()
    let init : TranslateState := {
      fileName := fileName
      gctx := gctx
      fvarIsOp := fvarIsOp
      modifiesMap := modMap
      globalVarTypes := varTypes
    }
    let act : TranslateM Core.Program := do
      let decls := (← cmds.mapM toCoreDecls).toList.flatten
      return { decls := decls }
    act.run' init

open Lean.Parser in

/-- Parse Boole syntax using generated `BooleDDM.Program.ofAst`. -/
def getProgram (p : Strata.Program) : Except DiagnosticModel Boole.Program := do
  let cmds : Array Arg := p.commands.map ArgF.op
  let progOp : Operation :=
    { ann := default
      name := q`Boole.prog
      args := #[.seq default .spacePrefix cmds] }
  match BooleDDM.Program.ofAst progOp with
  | .ok prog => return prog
  | .error e => throw (.fromMessage e)

def typeCheck (p : Strata.Program) (options : Core.VerifyOptions := .default) : Except DiagnosticModel Core.Program := do
  let prog ← getProgram p
  let coreProg ← toCoreProgram prog p.globalContext
  Core.typeCheck options coreProg

open Lean.Parser in
def verify
    (smtsolver : String) (env : Strata.Program)
    (ictx : InputContext := Inhabited.default)
    (proceduresToVerify : Option (List String) := none)
    (options : Core.VerifyOptions := .default)
    (tempDir : Option String := .none)
    : IO Core.VCResults := do
  let options := { options with solver := smtsolver }
  match getProgram env with
  | .error e =>
    throw <| IO.Error.userError (toString (e.format (some ictx.fileMap)))
  | .ok prog =>
    if options.verbose >= .normal then
      dbg_trace f!"\n\n[DEBUG] Boole program:\n{Boole.formatProgram prog env.globalContext env.dialects}"
    match toCoreProgram prog env.globalContext ictx.fileName with
    | .error e =>
      throw <| IO.Error.userError (toString (e.format (some ictx.fileMap)))
    | .ok cp =>
      let runner tempPath :=
        EIO.toIO (fun dm => IO.Error.userError (toString (dm.format (some ictx.fileMap))))
          (Core.verify cp tempPath proceduresToVerify options)
      match tempDir with
      | .none =>
        IO.FS.withTempDir runner
      | .some path =>
        IO.FS.createDirAll ⟨path⟩
        runner ⟨path⟩

end Strata.Boole
