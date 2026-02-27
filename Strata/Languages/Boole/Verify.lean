/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boole.DDMTransform.Parse
import Strata.Languages.Core.Verifier
import Strata.DL.Imperative.Stmt

namespace BooleDDM

-- set_option trace.Strata.generator true in
#strata_gen Boole

end BooleDDM

namespace Strata.Boole

open Lambda

/--
Boole verification pipeline:

`Strata.Program` -> `BooleDDM.Program.ofAst` -> `BooleDDM.Program`
-> `toCoreProgram` -> `Core.Program` -> `Core.verify`
-/
abbrev BooleTy := BooleDDM.BooleType SourceRange
abbrev Expr := BooleDDM.Expr SourceRange
abbrev Program := BooleDDM.Program SourceRange

structure TranslateState where
  fileName : String := ""
  fvars : Array String := #[]
  fvarIsOp : Array Bool := #[]
  tyBVars : Array String := #[]
  bvars : Array Core.Expression.Expr := #[]
  labelCounter : Nat := 0
  globalVarCounter : Nat := 0

abbrev TranslateM := StateT TranslateState (Except DiagnosticModel)

def mkIdent (name : String) : Core.Expression.Ident :=
  ⟨name, .unres⟩

def throwAt (m : SourceRange) (msg : String) : TranslateM α := do
  throw (.withRange ⟨⟨(← get).fileName⟩, m⟩ msg)

def defaultLabel (m : SourceRange) (pfx : String) (l? : Option (BooleDDM.Label SourceRange)) : TranslateM String := do
  match l? with
  | some (.label _ ⟨_, l⟩) => return l
  | none =>
    let i := (← get).labelCounter
    modify fun s => { s with labelCounter := i + 1 }
    return s!"{pfx}_{i}_{m.start}"

def withTypeBVars (xs : List String) (k : TranslateM α) : TranslateM α := do
  let old := (← get).tyBVars
  modify fun s => { s with tyBVars := old ++ xs.toArray }
  let out ← k
  modify fun s => { s with tyBVars := old }
  return out

def withBVars (xs : List String) (k : TranslateM α) : TranslateM α := do
  let old := (← get).bvars
  let fresh := xs.toArray.map (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr))
  modify fun s => { s with bvars := old ++ fresh }
  let out ← k
  modify fun s => { s with bvars := old }
  return out

def withBVarExprs (xs : Array Core.Expression.Expr) (k : TranslateM α) : TranslateM α := do
  let old := (← get).bvars
  modify fun s => { s with bvars := old ++ xs }
  let out ← k
  modify fun s => { s with bvars := old }
  return out

def getTypeBVarName (m : SourceRange) (i : Nat) : TranslateM String := do
  let xs := (← get).tyBVars
  if i < xs.size then
    match xs[(xs.size - i - 1)]? with
    | some n => return n
    | none => throwAt m s!"Unknown bound type variable with index {i}"
  else
    throwAt m s!"Unknown bound type variable with index {i}"

def getFVarName (m : SourceRange) (i : Nat) : TranslateM String := do
  match (← get).fvars[i]? with
  | some n => return n
  | none => throwAt m s!"Unknown free variable with index {i}"

def getFVarIsOp (m : SourceRange) (i : Nat) : TranslateM Bool := do
  match (← get).fvarIsOp[i]? with
  | some b => return b
  | none => throwAt m s!"Unknown free variable with index {i}"

def getBVarExpr (m : SourceRange) (i : Nat) : TranslateM Core.Expression.Expr := do
  let xs := (← get).bvars
  if i < xs.size then
    match xs[(xs.size - i - 1)]? with
    | some (.bvar _ _) => return (.bvar () i)
    | some e => return e
    | none => throwAt m s!"Unknown bound variable with index {i}"
  else
    throwAt m s!"Unknown bound variable with index {i}"

def typeArgsToList : BooleDDM.TypeArgs SourceRange → List String
  | .type_args _ ⟨_, xs⟩ =>
    xs.toList.map fun
      | .type_var _ ⟨_, n⟩ => n

def bindingsToList : BooleDDM.Bindings SourceRange → List (BooleDDM.Binding SourceRange)
  | .mkBindings _ ⟨_, xs⟩ => xs.toList

def declListToList : BooleDDM.DeclList SourceRange → List (BooleDDM.Bind SourceRange)
  | .declAtom _ b => [b]
  | .declPush _ bs b => declListToList bs ++ [b]

def monoDeclListToList : BooleDDM.MonoDeclList SourceRange → List (BooleDDM.MonoBind SourceRange)
  | .monoDeclAtom _ b => [b]
  | .monoDeclPush _ bs b => monoDeclListToList bs ++ [b]

def constructorListToList : BooleDDM.ConstructorList SourceRange → List (BooleDDM.Constructor SourceRange)
  | .constructorListAtom _ c => [c]
  | .constructorListPush _ cs c => constructorListToList cs ++ [c]

def toCoreMetaData (sr : SourceRange) : TranslateM (Imperative.MetaData Core.Expression) := do
  let file := (← get).fileName
  let uri : Uri := .file file
  let fileRangeElt := ⟨Imperative.MetaData.fileRange, .fileRange ⟨uri, sr⟩⟩
  return #[fileRangeElt]

def toCoreMonoType (t : BooleTy) : TranslateM Lambda.LMonoTy := do
  match t with
  | .bvar m n => return .ftvar (← getTypeBVarName m n)
  | .tvar _ n => return .ftvar n
  | .fvar m i args => return .tcons (← getFVarName m i) (← args.mapM toCoreMonoType).toList
  | .arrow _ a b => return .arrow (← toCoreMonoType a) (← toCoreMonoType b)
  | .bool _ => return .bool
  | .int _ => return .int
  | .bv1 _ => return .bitvec 1
  | .bv8 _ => return .bitvec 8
  | .bv16 _ => return .bitvec 16
  | .bv32 _ => return .bitvec 32
  | .bv64 _ => return .bitvec 64
  | .Map _ v k => return .tcons "Map" [← toCoreMonoType k, ← toCoreMonoType v]
  | _ => throwAt default "Unsupported type"

def toCoreType (t : BooleTy) : TranslateM Core.Expression.Ty := do
  return .forAll [] (← toCoreMonoType t)

def toCoreBinding (b : BooleDDM.Binding SourceRange) : TranslateM (Core.Expression.Ident × Lambda.LMonoTy) := do
  match b with
  | .mkBinding _ ⟨_, n⟩ tp =>
    match tp with
    | .expr ty => return (mkIdent n, ← toCoreMonoType ty)
    | .type m => throwAt m "Unexpected Type parameter in term binding"

def toCoreBind (b : BooleDDM.Bind SourceRange) : TranslateM (Core.Expression.Ident × Core.Expression.Ty) := do
  match b with
  | .bind_mk _ ⟨_, n⟩ _ ty => return (mkIdent n, ← toCoreType ty)

def toCoreMonoBind (b : BooleDDM.MonoBind SourceRange) : TranslateM (Core.Expression.Ident × Lambda.LMonoTy) := do
  match b with
  | .mono_bind_mk _ ⟨_, n⟩ ty => return (mkIdent n, ← toCoreMonoType ty)

def toCoreTypedUn (m : SourceRange) (ty : BooleTy) (op : String) (a : Core.Expression.Expr) : TranslateM Core.Expression.Expr := do
  let .int _ := ty
    | throwAt m s!"Unsupported typed operator type: {repr ty}"
  let bop : Core.Expression.Expr := .op () ⟨s!"Int.{op}", .unres⟩ none
  return .app () bop a

def toCoreTypedBin (m : SourceRange) (ty : BooleTy) (op : String) (a b : Core.Expression.Expr) : TranslateM Core.Expression.Expr := do
  let .int _ := ty
    | throwAt m s!"Unsupported typed operator type: {repr ty}"
  let bop : Core.Expression.Expr := .op () ⟨s!"Int.{op}", .unres⟩ none
  return .mkApp () bop [a, b]

mutual

def toCoreQuant
    (isForall : Bool)
    (ds : BooleDDM.DeclList SourceRange)
    (body : Boole.Expr) : TranslateM Core.Expression.Expr := do
  let decls := declListToList ds
  let tys ← decls.mapM fun (.bind_mk _ _ _ ty) => toCoreMonoType ty
  let qBVars : Array Core.Expression.Expr := (decls.toArray.mapIdx fun i _ => .bvar () i)
  let q := if isForall then .all else .exist
  let body' ← withBVarExprs qBVars (toCoreExpr body)
  return tys.foldr (fun ty acc => .quant () q (some ty) (.bvar () 0) acc) body'

def toCoreExpr (e : Boole.Expr) : TranslateM Core.Expression.Expr := do
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
  | .map_get _ _ _ a i => return Lambda.LExpr.mkApp () Core.mapSelectOp [← toCoreExpr a, ← toCoreExpr i]
  | .map_set _ _ _ a i v => return Lambda.LExpr.mkApp () Core.mapUpdateOp [← toCoreExpr a, ← toCoreExpr i, ← toCoreExpr v]
  | .btrue _ => return .true ()
  | .bfalse _ => return .false ()
  | .and _ a b => return Lambda.LExpr.mkApp () Core.boolAndOp [← toCoreExpr a, ← toCoreExpr b]
  | .or _ a b => return Lambda.LExpr.mkApp () Core.boolOrOp [← toCoreExpr a, ← toCoreExpr b]
  | .equiv _ a b => return Lambda.LExpr.mkApp () Core.boolEquivOp [← toCoreExpr a, ← toCoreExpr b]
  | .implies _ a b => return Lambda.LExpr.mkApp () Core.boolImpliesOp [← toCoreExpr a, ← toCoreExpr b]
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
  | .old _ _ a => return .app () Core.polyOldOp (← toCoreExpr a)
  | .forall _ ds body
  | .forallT _ ds _ body => toCoreQuant true ds body
  | .exists _ ds body
  | .existsT _ ds _ body => toCoreQuant false ds body
  | _ => throw (.fromMessage s!"Unsupported expression: {repr e}")

end

def nestMapSet (base : Core.Expression.Expr) (idxs : List Core.Expression.Expr) (rhs : Core.Expression.Expr) : Core.Expression.Expr :=
  match idxs with
  | [] => rhs
  | [i] => Lambda.LExpr.mkApp () Core.mapUpdateOp [base, i, rhs]
  | i :: rest =>
    let first := Lambda.LExpr.mkApp () Core.mapSelectOp [base, i]
    let inner := rest.dropLast.foldl (fun acc j => Lambda.LExpr.mkApp () Core.mapSelectOp [acc, j]) first
    let inner' := Lambda.LExpr.mkApp () Core.mapUpdateOp [inner, rest.getLast!, rhs]
    Lambda.LExpr.mkApp () Core.mapUpdateOp [base, i, inner']

def toCoreInvariants (is : BooleDDM.Invariants SourceRange) : TranslateM (List Core.Expression.Expr) := do
  go [] is
where
  go (acc : List Core.Expression.Expr) : BooleDDM.Invariants SourceRange → TranslateM (List Core.Expression.Expr)
    | .nilInvariants _ => return acc.reverse
    | .consInvariants _ e rest => do
      let e' ← toCoreExpr e
      let acc := e' :: acc
      go acc rest

def lowerFor
    (m : SourceRange)
    (id : Core.Expression.Ident)
    (ty : Lambda.LMonoTy)
    (initExpr guardExpr stepExpr : Core.Expression.Expr)
    (invs : List Core.Expression.Expr)
    (body : List Core.Statement) : TranslateM Core.Statement := do
  let initStmt : Core.Statement := .cmd (.cmd (.init id (.forAll [] ty) initExpr (← toCoreMetaData m)))
  let stepStmt : Core.Statement := .cmd (.cmd (.set id stepExpr (← toCoreMetaData m)))
  let loopBody := body ++ [stepStmt]
  return .block "for" [initStmt, .loop guardExpr none invs loopBody (← toCoreMetaData m)] (← toCoreMetaData m)

def lowerVarStatement (ds : BooleDDM.DeclList SourceRange) : TranslateM (List Core.Statement) := do
  let mut out : List Core.Statement := []
  let mut newBVars : List Core.Expression.Expr := []
  for d in declListToList ds do
    let (id, ty) ← toCoreBind d
    let n := (← get).globalVarCounter
    modify fun st => { st with globalVarCounter := n + 1 }
    let initName := mkIdent s!"init_{id.name}_{n}"
    newBVars := newBVars ++ [(.fvar () id none : Core.Expression.Expr)]
    out := out ++ [.cmd (.cmd (.init id ty (some (.fvar () initName none)) (← toCoreMetaData default)))]
  modify fun st => { st with bvars := st.bvars ++ newBVars.toArray }
  return out

mutual

def toCoreBlock (b : BooleDDM.Block SourceRange) : TranslateM (List Core.Statement) := do
  match b with
  | .block _ ⟨_, ss⟩ =>
    let mut out : List Core.Statement := []
    for s in ss do
      match s with
      | .varStatement _ ds =>
        out := out ++ (← lowerVarStatement ds)
      | _ =>
        out := out ++ [← toCoreStmt s]
    return out

def toCoreStmt (s : BooleDDM.Statement SourceRange) : TranslateM Core.Statement := do
  match s with
  | .varStatement m ds =>
    let out ← lowerVarStatement ds
    let some first := out.head?
      | throwAt default "Empty var declaration list"
    match ds with
    | .declAtom _ _ => return first
    | _ => return .block "var" out (← toCoreMetaData m)
  | .initStatement m ty ⟨_, n⟩ e =>
    let rhs ← toCoreExpr e
    modify fun st => { st with bvars := st.bvars.push (.fvar () (mkIdent n) none) }
    return .cmd (.cmd (.init (mkIdent n) (← toCoreType ty) rhs (← toCoreMetaData m)))
  | .assign m _ lhs rhs =>
    let rec lhsParts (lhs : BooleDDM.Lhs SourceRange) : TranslateM (String × List Core.Expression.Expr) := do
      match lhs with
      | .lhsIdent _ ⟨_, n⟩ => return (n, [])
      | .lhsArray _ _ l i =>
        let (n, is) ← lhsParts l
        return (n, is ++ [← toCoreExpr i])
    let (n, idxs) ← lhsParts lhs
    let base := .fvar () (mkIdent n) none
    return .cmd (.cmd (.set (mkIdent n) (nestMapSet base idxs (← toCoreExpr rhs)) (← toCoreMetaData m)))
  | .assume m ⟨_, l?⟩ e =>
    return .cmd (.cmd (.assume (← defaultLabel m "assume" l?) (← toCoreExpr e) (← toCoreMetaData m)))
  | .assert m rc? ⟨_, l?⟩ e =>
    let md ← toCoreMetaData m
    let md := if rc? matches ⟨_, some _⟩ then md.pushElem Imperative.MetaData.reachCheck (.switch true) else md
    return .cmd (.cmd (.assert (← defaultLabel m "assert" l?) (← toCoreExpr e) md))
  | .cover m rc? ⟨_, l?⟩ e =>
    let md ← toCoreMetaData m
    let md := if rc? matches ⟨_, some _⟩ then md.pushElem Imperative.MetaData.reachCheck (.switch true) else md
    return .cmd (.cmd (.cover (← defaultLabel m "cover" l?) (← toCoreExpr e) md))
  | .if_statement m c t e =>
    let thenb ← withBVars [] (toCoreBlock t)
    let elseb ← withBVars [] <| match e with
      | .else0 _ => return []
      | .else1 _ b => toCoreBlock b
    return .ite (← toCoreExpr c) thenb elseb (← toCoreMetaData m)
  | .havoc_statement m ⟨_, n⟩ =>
    return .cmd (.cmd (.havoc (mkIdent n) (← toCoreMetaData m)))
  | .while_statement m g invs b =>
    return .loop (← toCoreExpr g) none (← toCoreInvariants invs) (← withBVars [] (toCoreBlock b)) (← toCoreMetaData m)
  | .call_statement m ⟨_, lhs⟩ ⟨_, n⟩ ⟨_, args⟩ =>
    return .cmd (.call (lhs.toList.map (mkIdent ·.val)) n (← args.toList.mapM toCoreExpr) (← toCoreMetaData m))
  | .call_unit_statement m ⟨_, n⟩ ⟨_, args⟩ =>
    return .cmd (.call [] n (← args.toList.mapM toCoreExpr) (← toCoreMetaData m))
  | .block_statement m ⟨_, l⟩ b =>
    return .block l (← withBVars [] (toCoreBlock b)) (← toCoreMetaData m)
  | .exit_statement m ⟨_, l⟩ =>
    return .exit l (← toCoreMetaData m)
  | .exit_unlabeled_statement m =>
    return .exit none (← toCoreMetaData m)
  | .funcDecl_statement m _ _ _ _ _ _ _ => throwAt m "Local function declarations are not yet supported"
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
      let guard := Lambda.LExpr.mkApp () Core.intLeOp [.fvar () id none, limitExpr]
      let stepExpr ← match step? with
        | none => pure (.intConst () 1)
        | some (.step _ e) => toCoreExpr e
      let body ← withBVars [] (toCoreBlock body)
      lowerFor
        m id ty
        initExpr
        guard
        (Lambda.LExpr.mkApp () Core.intAddOp [.fvar () id none, stepExpr])
        (← toCoreInvariants invs)
        body
  | .for_down_to_by_statement m v init limit ⟨_, step?⟩ invs body =>
    let (id, ty) ← toCoreMonoBind v
    let limitExpr ← toCoreExpr limit
    withBVars [id.name] do
      let initExpr ← toCoreExpr init
      let guard := Lambda.LExpr.mkApp () Core.intLeOp [limitExpr, .fvar () id none]
      let stepExpr ← match step? with
        | none => pure (.intConst () 1)
        | some (.step _ e) => toCoreExpr e
      let body ← withBVars [] (toCoreBlock body)
      lowerFor
        m id ty
        initExpr
        guard
        (Lambda.LExpr.mkApp () Core.intSubOp [.fvar () id none, stepExpr])
        (← toCoreInvariants invs)
        body
  | .array_assign_2d m arr i j rhs =>
    let baseExpr ← toCoreExpr arr
    match baseExpr with
    | .fvar _ id _ =>
      return .cmd (.cmd (.set id (nestMapSet baseExpr [← toCoreExpr i, ← toCoreExpr j] (← toCoreExpr rhs)) (← toCoreMetaData m)))
    | _ => throwAt m "2D array assignment target must be a variable"

end

def checkAttrOf (f? : Option (BooleDDM.Free SourceRange)) : Core.Procedure.CheckAttr :=
  match f? with
  | some _ => .Free
  | none => .Default

def toCoreDatatypeConstr
    (dtypeName : String)
    (c : BooleDDM.Constructor SourceRange) : TranslateM (Lambda.LConstr Core.Visibility) := do
  match c with
  | .constructor_mk _ ⟨_, cname⟩ ⟨_, fields?⟩ =>
    let args ← match fields? with
      | none => pure []
      | some ⟨_, fs⟩ => fs.toList.mapM toCoreBinding
    return { name := mkIdent cname
             args := args
             testerName := s!"{dtypeName}..is{cname}" }

def toCoreDatatype
    (m : SourceRange)
    (dtypeName : String)
    (typeParams : List String)
    (ctors : BooleDDM.ConstructorList SourceRange) : TranslateM (Lambda.LDatatype Core.Visibility) := do
  let ctorList := constructorListToList ctors
  let some _ := ctorList.head?
    | throwAt m s!"Datatype {dtypeName} must have at least one constructor"
  let constrs ← ctorList.mapM (toCoreDatatypeConstr dtypeName)
  match h : constrs with
  | [] => throwAt m s!"Datatype {dtypeName} must have at least one constructor"
  | _ :: _ =>
    return { name := dtypeName
             typeArgs := typeParams
             constrs := constrs
             constrs_ne := by simp [h] }

def toCoreSpecElts (_m : SourceRange) (pname : String) (elts : Array (BooleDDM.SpecElt SourceRange)) : TranslateM Core.Procedure.Spec := do
  let mut modifies : List (List Core.Expression.Ident) := []
  let mut reqs : List (Core.CoreLabel × Core.Procedure.Check) := []
  let mut enss : List (Core.CoreLabel × Core.Procedure.Check) := []
  for e in elts.toList do
    match e with
    | .modifies_spec _ ⟨_, ns⟩ =>
      modifies := ns.toList.map (mkIdent ∘ Ann.val) :: modifies
    | .requires_spec em ⟨_, l?⟩ ⟨_, free?⟩ cond =>
      reqs := (← defaultLabel em s!"{pname}_requires" l?, { expr := ← toCoreExpr cond, attr := checkAttrOf free? }) :: reqs
    | .ensures_spec em ⟨_, l?⟩ ⟨_, free?⟩ cond =>
      enss := (← defaultLabel em s!"{pname}_ensures" l?, { expr := ← toCoreExpr cond, attr := checkAttrOf free? }) :: enss
  return { modifies := modifies.reverse.flatten, preconditions := reqs.reverse, postconditions := enss.reverse }

def toCoreSpec (m : SourceRange) (pname : String) (spec? : Option (BooleDDM.Spec SourceRange)) : TranslateM Core.Procedure.Spec := do
  match spec? with
  | none => return { modifies := [], preconditions := [], postconditions := [] }
  | some (.spec_mk _ ⟨_, elts⟩) =>
    toCoreSpecElts m pname elts

def registerCommandSymbols (cmd : BooleDDM.Command SourceRange) : List (String × Bool) :=
  match cmd with
  | .command_typedecl _ ⟨_, n⟩ _ => [(n, false)]
  | .command_forward_typedecl _ ⟨_, n⟩ _ => [(n, false)]
  | .command_typesynonym _ ⟨_, n⟩ _ _ _ => [(n, false)]
  | .command_constdecl _ ⟨_, n⟩ _ _ => [(n, true)]
  | .command_fndecl _ ⟨_, n⟩ _ _ _ => [(n, true)]
  | .command_fndef _ ⟨_, n⟩ _ _ _ _ _ _ => [(n, true)]
  | .command_var _ (.bind_mk _ ⟨_, n⟩ _ _) => [(n, false)]
  -- Procedure names are referenced by call statements directly and are not Expr.fvar symbols.
  | .command_procedure _ _ _ _ _ _ _ => []
  | .command_datatype _ ⟨_, n⟩ _ _ => [(n, false)]
  | .command_mutual _ ⟨_, cmds⟩ =>
    (cmds.map registerCommandSymbols).toList.flatten
  | .command_block _ _ => []
  | .command_axiom _ _ _ => []
  | .command_distinct _ _ _ => []

def initFVars (p : Boole.Program) : Array String × Array Bool :=
  match p with
  | .prog _ ⟨_, cmds⟩ =>
    let syms := (cmds.map registerCommandSymbols).toList.flatten
    (syms.map (·.1) |>.toArray, syms.map (·.2) |>.toArray)

def toCoreDecls (cmd : BooleDDM.Command SourceRange) : TranslateM (List Core.Decl) := do
  match cmd with
  | .command_procedure m ⟨_, n⟩ ⟨_, targs?⟩ ins ⟨_, outs?⟩ ⟨_, spec?⟩ ⟨_, body?⟩ =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      let inputs ← (bindingsToList ins).mapM toCoreBinding
      let outputs ← match outs? with
        | none => pure []
        | some os => (monoDeclListToList os).mapM toCoreMonoBind
      let inputNames := inputs.map (·.fst.name)
      let outputNames := outputs.map (·.fst.name)
      let spec ← withBVars (inputNames ++ outputNames) (toCoreSpec m n spec?)
      let body ← match body? with
        | none => pure []
        | some b => withBVars (inputNames ++ outputNames) (toCoreBlock b)
      return [Core.Decl.proc {
        header := { name := mkIdent n, typeArgs := tys, inputs := inputs, outputs := outputs }
        spec := spec
        body := body
      }]
  | .command_typedecl _ ⟨_, n⟩ ⟨_, args?⟩
  | .command_forward_typedecl _ ⟨_, n⟩ ⟨_, args?⟩ =>
    let numargs := match args? with | none => 0 | some bs => (bindingsToList bs).length
    return [.type (.con { name := n, numargs := numargs })]
  | .command_typesynonym _ ⟨_, n⟩ ⟨_, args?⟩ _ rhs =>
    let tys := match args? with | none => [] | some bs => (bindingsToList bs).map (fun | .mkBinding _ ⟨_, x⟩ _ => x)
    withTypeBVars tys do
      return [.type (.syn { name := n, typeArgs := tys, type := ← toCoreMonoType rhs })]
  | .command_constdecl _ ⟨_, n⟩ ⟨_, targs?⟩ ret =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      return [.func { name := mkIdent n, typeArgs := tys, inputs := [], output := ← toCoreMonoType ret, body := none, concreteEval := none, attr := #[], axioms := [] }]
  | .command_fndecl _ ⟨_, n⟩ ⟨_, targs?⟩ bs ret =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      return [.func { name := mkIdent n, typeArgs := tys, inputs := ← (bindingsToList bs).mapM toCoreBinding, output := ← toCoreMonoType ret, body := none, concreteEval := none, attr := #[], axioms := [] }]
  | .command_fndef m ⟨_, n⟩ ⟨_, targs?⟩ bs ret ⟨_, pres⟩ body ⟨_, inline?⟩ =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      let bsList := bindingsToList bs
      let inputs ← bsList.mapM toCoreBinding
      let inputNames := bsList.map fun (.mkBinding _ ⟨_, x⟩ _) => x
      let pres ← withBVars inputNames (toCoreSpecElts m n pres)
      let pres := pres.preconditions.map (fun (_, c) => ⟨c.expr, ()⟩)
      let body ← withBVars inputNames (toCoreExpr body)
      return [.func { name := mkIdent n, typeArgs := tys, inputs := inputs, output := ← toCoreMonoType ret, body := some body, concreteEval := none, attr := if inline?.isSome then #[.inline] else #[], axioms := [], preconditions := pres }]
  | .command_var _ b =>
    let (id, ty) ← toCoreBind b
    let i := (← get).globalVarCounter
    modify fun s => { s with globalVarCounter := i + 1 }
    return [.var id ty (some (.fvar () (mkIdent s!"init_{id.name}_{i}") none))]
  | .command_axiom m ⟨_, l?⟩ e =>
    return [.ax { name := ← defaultLabel m "axiom" l?, e := ← toCoreExpr e }]
  | .command_distinct m ⟨_, l?⟩ ⟨_, es⟩ =>
    return [.distinct (mkIdent (← defaultLabel m "distinct" l?)) (← es.toList.mapM toCoreExpr)]
  | .command_block _ b =>
    return [.proc {
      header := { name := mkIdent "", typeArgs := [], inputs := [], outputs := [] }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := ← toCoreBlock b
    }]
  | .command_datatype m ⟨_, dtypeName⟩ ⟨_, typeParams?⟩ ctors =>
    let typeParams := match typeParams? with
      | none => []
      | some bs => (bindingsToList bs).map (fun | .mkBinding _ ⟨_, n⟩ _ => n)
    withTypeBVars typeParams do
      return [.type (.data [← toCoreDatatype m dtypeName typeParams ctors])]
  | .command_mutual m ⟨_, cmds⟩ =>
    let mut dts : List (Lambda.LDatatype Core.Visibility) := []
    for cmd in cmds.toList do
      match cmd with
      | .command_datatype dm ⟨_, dtypeName⟩ ⟨_, typeParams?⟩ ctors =>
        let typeParams := match typeParams? with
          | none => []
          | some bs => (bindingsToList bs).map (fun | .mkBinding _ ⟨_, n⟩ _ => n)
        let dt ← withTypeBVars typeParams do
          toCoreDatatype dm dtypeName typeParams ctors
        dts := dts ++ [dt]
      | _ =>
        throwAt m "Mutual blocks currently support only datatype declarations"
    let some _ := dts.head?
      | throwAt m "Mutual block must contain at least one datatype declaration"
    return [.type (.data dts)]

def toCoreProgram (p : Boole.Program) : Except DiagnosticModel Core.Program := do
  match p with
  | .prog _ ⟨_, cmds⟩ =>
    let (fvars, fvarIsOp) := initFVars p
    let init : TranslateState := { fvars := fvars, fvarIsOp := fvarIsOp }
    let act : TranslateM Core.Program := do
      let decls := (← cmds.mapM toCoreDecls).toList.flatten
      pure { decls := decls }
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

def typeCheck (p : Strata.Program) (options : Options := Options.default) : Except DiagnosticModel Core.Program := do
  let prog ← getProgram p
  let coreProg ← toCoreProgram prog
  Core.typeCheck options coreProg

open Lean.Parser in
def verify
    (smtsolver : String) (env : Strata.Program)
    (ictx : InputContext := Inhabited.default)
    (proceduresToVerify : Option (List String) := none)
    (options : Options := Options.default)
    (tempDir : Option String := .none)
    : IO Core.VCResults := do
  let options := { options with solver := smtsolver }
  match getProgram env with
  | .error e =>
    throw <| IO.Error.userError (toString (e.format (some ictx.fileMap)))
  | .ok prog =>
    match toCoreProgram prog with
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
