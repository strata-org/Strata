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
  fvars : Array String := #[]
  fvarIsOp : Array Bool := #[]
  tyBVars : Array String := #[]
  bvars : Array Core.Expression.Expr := #[]
  labelCounter : Nat := 0
  globalVarCounter : Nat := 0

abbrev TranslateM := StateT TranslateState (Except DiagnosticModel)

private def mkIdent (name : String) : Core.Expression.Ident :=
  ⟨name, .unres⟩

private def throwAt (m : SourceRange) (msg : String) : TranslateM α :=
  throw (.withRange ⟨⟨""⟩, m⟩ msg)

private def defaultLabel (m : SourceRange) (pfx : String) (l? : Option (BooleDDM.Label SourceRange)) : TranslateM String :=
  match l? with
  | some (.label _ ⟨_, l⟩) => pure l
  | none => do
    let i := (← get).labelCounter
    modify fun s => { s with labelCounter := i + 1 }
    pure s!"{pfx}_{i}_{m.start}"

private def withTypeBVars (xs : List String) (k : TranslateM α) : TranslateM α := do
  let old := (← get).tyBVars
  modify fun s => { s with tyBVars := old ++ xs.toArray }
  let out ← k
  modify fun s => { s with tyBVars := old }
  pure out

private def withBVars (xs : List String) (k : TranslateM α) : TranslateM α := do
  let old := (← get).bvars
  let fresh := xs.toArray.map (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr))
  modify fun s => { s with bvars := old ++ fresh }
  let out ← k
  modify fun s => { s with bvars := old }
  pure out

private def withBVarExprs (xs : Array Core.Expression.Expr) (k : TranslateM α) : TranslateM α := do
  let old := (← get).bvars
  modify fun s => { s with bvars := old ++ xs }
  let out ← k
  modify fun s => { s with bvars := old }
  pure out

private def getTypeBVarName (m : SourceRange) (i : Nat) : TranslateM String := do
  let xs := (← get).tyBVars
  if i < xs.size then
    match xs[(xs.size - i - 1)]? with
    | some n => pure n
    | none => throwAt m s!"Unknown bound type variable with index {i}"
  else
    throwAt m s!"Unknown bound type variable with index {i}"

private def getFVarName (m : SourceRange) (i : Nat) : TranslateM String := do
  match (← get).fvars[i]? with
  | some n => pure n
  | none => throwAt m s!"Unknown free variable with index {i}"

private def getFVarIsOp (m : SourceRange) (i : Nat) : TranslateM Bool := do
  match (← get).fvarIsOp[i]? with
  | some b => pure b
  | none => throwAt m s!"Unknown free variable with index {i}"

private def getBVarExpr (m : SourceRange) (i : Nat) : TranslateM Core.Expression.Expr := do
  let xs := (← get).bvars
  if i < xs.size then
    match xs[(xs.size - i - 1)]? with
    | some (.bvar _ _) => pure (.bvar () i)
    | some e => pure e
    | none => throwAt m s!"Unknown bound variable with index {i}"
  else
    throwAt m s!"Unknown bound variable with index {i}"

private def typeArgsToList : BooleDDM.TypeArgs SourceRange → List String
  | .type_args _ ⟨_, xs⟩ =>
    xs.toList.map fun
      | .type_var _ ⟨_, n⟩ => n

private def bindingsToList : BooleDDM.Bindings SourceRange → List (BooleDDM.Binding SourceRange)
  | .mkBindings _ ⟨_, xs⟩ => xs.toList

private def declListToList : BooleDDM.DeclList SourceRange → List (BooleDDM.Bind SourceRange)
  | .declAtom _ b => [b]
  | .declPush _ bs b => declListToList bs ++ [b]

private def monoDeclListToList : BooleDDM.MonoDeclList SourceRange → List (BooleDDM.MonoBind SourceRange)
  | .monoDeclAtom _ b => [b]
  | .monoDeclPush _ bs b => monoDeclListToList bs ++ [b]

private def constructorListToList : BooleDDM.ConstructorList SourceRange → List (BooleDDM.Constructor SourceRange)
  | .constructorListAtom _ c => [c]
  | .constructorListPush _ cs c => constructorListToList cs ++ [c]

mutual

partial def toCoreMonoType (t : BooleTy) : TranslateM Lambda.LMonoTy := do
  match t with
  | .bvar m n => pure <| .ftvar (← getTypeBVarName m n)
  | .tvar _ n => pure <| .ftvar n
  | .fvar m i args => pure <| .tcons (← getFVarName m i) (← args.toList.mapM toCoreMonoType)
  | .arrow _ a b => pure <| .arrow (← toCoreMonoType a) (← toCoreMonoType b)
  | .bool _ => pure .bool
  | .int _ => pure .int
  | .Map _ d r => pure <| .tcons "Map" [← toCoreMonoType d, ← toCoreMonoType r]
  | _ => throwAt default "Unsupported type"

partial def toCoreType (t : BooleTy) : TranslateM Core.Expression.Ty := do
  pure <| .forAll [] (← toCoreMonoType t)

partial def toCoreBinding (b : BooleDDM.Binding SourceRange) : TranslateM (Core.Expression.Ident × Lambda.LMonoTy) := do
  match b with
  | .mkBinding _ ⟨_, n⟩ tp =>
    match tp with
    | .expr ty => pure (mkIdent n, ← toCoreMonoType ty)
    | .type m => throwAt m "Unexpected Type parameter in term binding"

partial def toCoreBind (b : BooleDDM.Bind SourceRange) : TranslateM (Core.Expression.Ident × Core.Expression.Ty) := do
  match b with
  | .bind_mk _ ⟨_, n⟩ _ ty => pure (mkIdent n, ← toCoreType ty)

partial def toCoreMonoBind (b : BooleDDM.MonoBind SourceRange) : TranslateM (Core.Expression.Ident × Lambda.LMonoTy) := do
  match b with
  | .mono_bind_mk _ ⟨_, n⟩ ty => pure (mkIdent n, ← toCoreMonoType ty)

private partial def toCoreTypedUn (m : SourceRange) (ty : BooleTy) (op : String) (a : Expr) : TranslateM Core.Expression.Expr := do
  let .int _ := ty
    | throwAt m s!"Unsupported typed operator type: {repr ty}"
  let bop : Core.Expression.Expr := .op () ⟨s!"Int.{op}", .unres⟩ none
  pure <| .app () bop (← toCoreExpr a)

private partial def toCoreTypedBin (m : SourceRange) (ty : BooleTy) (op : String) (a b : Expr) : TranslateM Core.Expression.Expr := do
  let .int _ := ty
    | throwAt m s!"Unsupported typed operator type: {repr ty}"
  let bop : Core.Expression.Expr := .op () ⟨s!"Int.{op}", .unres⟩ none
  pure <| Lambda.LExpr.mkApp () bop [← toCoreExpr a, ← toCoreExpr b]

private partial def toCoreQuant
    (isForall : Bool)
    (ds : BooleDDM.DeclList SourceRange)
    (body : Expr) : TranslateM Core.Expression.Expr := do
  let decls := declListToList ds
  let tys ← decls.mapM fun
    | .bind_mk _ _ _ ty => toCoreMonoType ty
  let qBVars : Array Core.Expression.Expr := (decls.toArray.mapIdx fun i _ => .bvar () i)
  let q := if isForall then .all else .exist
  let body' ← withBVarExprs qBVars (toCoreExpr body)
  pure <| tys.foldr (fun ty acc => .quant () q (some ty) (.bvar () 0) acc) body'

partial def toCoreExpr (e : Expr) : TranslateM Core.Expression.Expr := do
  match e with
  | .fvar m i =>
    let id := mkIdent (← getFVarName m i)
    if (← getFVarIsOp m i) then
      pure <| .op () id none
    else
      pure <| .fvar () id none
  | .bvar m i => getBVarExpr m i
  | .app _ f a => pure <| .app () (← toCoreExpr f) (← toCoreExpr a)
  | .not _ a => pure <| .app () Core.boolNotOp (← toCoreExpr a)
  | .natToInt _ ⟨_, n⟩ => pure <| .intConst () (Int.ofNat n)
  | .if _ _ c t f => pure <| .ite () (← toCoreExpr c) (← toCoreExpr t) (← toCoreExpr f)
  | .map_get _ _ _ a i => pure <| Lambda.LExpr.mkApp () Core.mapSelectOp [← toCoreExpr a, ← toCoreExpr i]
  | .map_set _ _ _ a i v => pure <| Lambda.LExpr.mkApp () Core.mapUpdateOp [← toCoreExpr a, ← toCoreExpr i, ← toCoreExpr v]
  | .btrue _ => pure <| .true ()
  | .bfalse _ => pure <| .false ()
  | .and _ a b => pure <| Lambda.LExpr.mkApp () Core.boolAndOp [← toCoreExpr a, ← toCoreExpr b]
  | .or _ a b => pure <| Lambda.LExpr.mkApp () Core.boolOrOp [← toCoreExpr a, ← toCoreExpr b]
  | .equiv _ a b => pure <| Lambda.LExpr.mkApp () Core.boolEquivOp [← toCoreExpr a, ← toCoreExpr b]
  | .implies _ a b => pure <| Lambda.LExpr.mkApp () Core.boolImpliesOp [← toCoreExpr a, ← toCoreExpr b]
  | .equal _ _ a b => pure <| .eq () (← toCoreExpr a) (← toCoreExpr b)
  | .not_equal _ _ a b => pure <| .app () Core.boolNotOp (.eq () (← toCoreExpr a) (← toCoreExpr b))
  | .le m ty a b => toCoreTypedBin m ty "Le" a b
  | .lt m ty a b => toCoreTypedBin m ty "Lt" a b
  | .ge m ty a b => toCoreTypedBin m ty "Ge" a b
  | .gt m ty a b => toCoreTypedBin m ty "Gt" a b
  | .neg_expr m ty a => toCoreTypedUn m ty "Neg" a
  | .add_expr m ty a b => toCoreTypedBin m ty "Add" a b
  | .sub_expr m ty a b => toCoreTypedBin m ty "Sub" a b
  | .mul_expr m ty a b => toCoreTypedBin m ty "Mul" a b
  | .div_expr m ty a b => toCoreTypedBin m ty "Div" a b
  | .mod_expr m ty a b => toCoreTypedBin m ty "Mod" a b
  | .forall _ ds body
  | .forallT _ ds _ body => toCoreQuant true ds body
  | .exists _ ds body
  | .existsT _ ds _ body => toCoreQuant false ds body
  | _ => throw (.fromMessage s!"Unsupported expression: {repr e}")

partial def nestMapSet (base : Core.Expression.Expr) (idxs : List Core.Expression.Expr) (rhs : Core.Expression.Expr) : Core.Expression.Expr :=
  match idxs with
  | [] => rhs
  | [i] => Lambda.LExpr.mkApp () Core.mapUpdateOp [base, i, rhs]
  | i :: rest =>
    let first := Lambda.LExpr.mkApp () Core.mapSelectOp [base, i]
    let inner := rest.dropLast.foldl (fun acc j => Lambda.LExpr.mkApp () Core.mapSelectOp [acc, j]) first
    let inner' := Lambda.LExpr.mkApp () Core.mapUpdateOp [inner, rest.getLast!, rhs]
    Lambda.LExpr.mkApp () Core.mapUpdateOp [base, i, inner']

partial def toCoreInvariant (is : BooleDDM.Invariants SourceRange) : TranslateM (Option Core.Expression.Expr) := do
  let rec go (acc? : Option Core.Expression.Expr) : BooleDDM.Invariants SourceRange → TranslateM (Option Core.Expression.Expr)
    | .nilInvariants _ => pure acc?
    | .consInvariants _ e rest => do
      let e' ← toCoreExpr e
      let acc? := match acc? with
        | none => some e'
        | some a => some (Lambda.LExpr.mkApp () Core.boolAndOp [a, e'])
      go acc? rest
  go none is

partial def lowerFor
    (id : Core.Expression.Ident)
    (ty : Lambda.LMonoTy)
    (initExpr guardExpr stepExpr : Core.Expression.Expr)
    (inv : Option Core.Expression.Expr)
    (body : List Core.Statement) : Core.Statement :=
  let initStmt : Core.Statement := .cmd (.cmd (.init id (.forAll [] ty) initExpr))
  let stepStmt : Core.Statement := .cmd (.cmd (.set id stepExpr))
  let loopBody := body ++ [stepStmt]
  .block "for" [initStmt, .loop guardExpr none inv loopBody]

private partial def lowerVarStatement (ds : BooleDDM.DeclList SourceRange) : TranslateM (List Core.Statement) := do
  let mut out : List Core.Statement := []
  let mut newBVars : List Core.Expression.Expr := []
  for d in declListToList ds do
    let (id, ty) ← toCoreBind d
    let n := (← get).globalVarCounter
    modify fun st => { st with globalVarCounter := n + 1 }
    let initName := mkIdent s!"init_{id.name}_{n}"
    newBVars := newBVars ++ [(.fvar () id none : Core.Expression.Expr)]
    out := out ++ [.cmd (.cmd (.init id ty (.fvar () initName none)))]
  modify fun st => { st with bvars := st.bvars ++ newBVars.toArray }
  pure out

partial def toCoreBlock (b : BooleDDM.Block SourceRange) : TranslateM (List Core.Statement) := do
  match b with
  | .block _ ⟨_, ss⟩ =>
    let mut out : List Core.Statement := []
    for s in ss.toList do
      match s with
      | .varStatement _ ds =>
        out := out ++ (← lowerVarStatement ds)
      | _ =>
        out := out ++ [← toCoreStmt s]
    pure out

partial def toCoreStmt (s : BooleDDM.Statement SourceRange) : TranslateM Core.Statement := do
  match s with
  | .varStatement _ ds =>
    let out ← lowerVarStatement ds
    let some first := out.head?
      | throwAt default "Empty var declaration list"
    match ds with
    | .declAtom _ _ => pure first
    | _ => pure <| .block "var" out
  | .initStatement _ ty ⟨_, n⟩ e =>
    let rhs ← toCoreExpr e
    modify fun st => { st with bvars := st.bvars.push (.fvar () (mkIdent n) none) }
    pure <| .cmd (.cmd (.init (mkIdent n) (← toCoreType ty) rhs))
  | .assign _ _ lhs rhs =>
    let rec lhsParts (lhs : BooleDDM.Lhs SourceRange) : TranslateM (String × List Core.Expression.Expr) := do
      match lhs with
      | .lhsIdent _ ⟨_, n⟩ => pure (n, [])
      | .lhsArray _ _ l i =>
        let (n, is) ← lhsParts l
        pure (n, is ++ [← toCoreExpr i])
    let (n, idxs) ← lhsParts lhs
    let base := .fvar () (mkIdent n) none
    pure <| .cmd (.cmd (.set (mkIdent n) (nestMapSet base idxs (← toCoreExpr rhs))))
  | .assume m ⟨_, l?⟩ e =>
    pure <| .cmd (.cmd (.assume (← defaultLabel m "assume" l?) (← toCoreExpr e)))
  | .assert m ⟨_, l?⟩ e =>
    pure <| .cmd (.cmd (.assert (← defaultLabel m "assert" l?) (← toCoreExpr e)))
  | .cover m ⟨_, l?⟩ e =>
    pure <| .cmd (.cmd (.cover (← defaultLabel m "cover" l?) (← toCoreExpr e)))
  | .if_statement _ c t e =>
    let thenb ← withBVars [] (toCoreBlock t)
    let elseb ← withBVars [] <| match e with
      | .else0 _ => pure []
      | .else1 _ b => toCoreBlock b
    pure <| .ite (← toCoreExpr c) thenb elseb
  | .havoc_statement _ ⟨_, n⟩ =>
    pure <| .cmd (.cmd (.havoc (mkIdent n)))
  | .while_statement _ g invs b =>
    pure <| .loop (← toCoreExpr g) none (← toCoreInvariant invs) (← withBVars [] (toCoreBlock b))
  | .call_statement _ ⟨_, lhs⟩ ⟨_, n⟩ ⟨_, args⟩ =>
    pure <| .cmd (.call (lhs.toList.map (mkIdent ·.val)) n (← args.toList.mapM toCoreExpr))
  | .call_unit_statement _ ⟨_, n⟩ ⟨_, args⟩ =>
    pure <| .cmd (.call [] n (← args.toList.mapM toCoreExpr))
  | .block_statement _ ⟨_, l⟩ b =>
    pure <| .block l (← withBVars [] (toCoreBlock b))
  | .goto_statement _ ⟨_, l⟩ =>
    pure <| .goto l
  | .funcDecl_statement m _ _ _ _ _ _ => throwAt m "Local function declarations are not yet supported"
  | .for_statement _ v init guard step invs body =>
    let (id, ty) ← toCoreMonoBind v
    withBVars [id.name] do
      let body ← withBVars [] (toCoreBlock body)
      pure <| lowerFor
        id ty
        (← toCoreExpr init)
        (← toCoreExpr guard)
        (← toCoreExpr step)
        (← toCoreInvariant invs)
        body
  | .for_to_by_statement _ v init limit ⟨_, step?⟩ invs body =>
    let (id, ty) ← toCoreMonoBind v
    let limitExpr ← toCoreExpr limit
    withBVars [id.name] do
      let initExpr ← toCoreExpr init
      let guard := Lambda.LExpr.mkApp () Core.intLeOp [.fvar () id none, limitExpr]
      let stepExpr ← match step? with
        | none => pure (.intConst () 1)
        | some (.step _ e) => toCoreExpr e
      let body ← withBVars [] (toCoreBlock body)
      pure <| lowerFor
        id ty
        initExpr
        guard
        (Lambda.LExpr.mkApp () Core.intAddOp [.fvar () id none, stepExpr])
        (← toCoreInvariant invs)
        body
  | .for_down_to_by_statement _ v init limit ⟨_, step?⟩ invs body =>
    let (id, ty) ← toCoreMonoBind v
    let limitExpr ← toCoreExpr limit
    withBVars [id.name] do
      let initExpr ← toCoreExpr init
      let guard := Lambda.LExpr.mkApp () Core.intLeOp [limitExpr, .fvar () id none]
      let stepExpr ← match step? with
        | none => pure (.intConst () 1)
        | some (.step _ e) => toCoreExpr e
      let body ← withBVars [] (toCoreBlock body)
      pure <| lowerFor
        id ty
        initExpr
        guard
        (Lambda.LExpr.mkApp () Core.intSubOp [.fvar () id none, stepExpr])
        (← toCoreInvariant invs)
        body
  | .array_assign_2d m _ _ _ _ => throwAt m "2D array assignment is not yet supported"

end

private def checkAttrOf (f? : Option (BooleDDM.Free SourceRange)) : Core.Procedure.CheckAttr :=
  match f? with
  | some _ => .Free
  | none => .Default

private def toCoreDatatypeConstr
    (dtypeName : String)
    (c : BooleDDM.Constructor SourceRange) : TranslateM (Lambda.LConstr Core.Visibility) := do
  match c with
  | .constructor_mk _ ⟨_, cname⟩ ⟨_, fields?⟩ =>
    let args ← match fields? with
      | none => pure []
      | some ⟨_, fs⟩ => fs.toList.mapM toCoreBinding
    pure
      { name := mkIdent cname
        args := args
        testerName := s!"{dtypeName}..is{cname}" }

private def toCoreDatatype
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
    pure
      { name := dtypeName
        typeArgs := typeParams
        constrs := constrs
        constrs_ne := by simp [h] }

private def toCoreSpec (_m : SourceRange) (pname : String) (spec? : Option (BooleDDM.Spec SourceRange)) : TranslateM Core.Procedure.Spec := do
  match spec? with
  | none => pure { modifies := [], preconditions := [], postconditions := [] }
  | some (.spec_mk _ ⟨_, elts⟩) =>
    let mut modifies : List Core.Expression.Ident := []
    let mut reqs : List (Core.CoreLabel × Core.Procedure.Check) := []
    let mut enss : List (Core.CoreLabel × Core.Procedure.Check) := []
    for e in elts.toList do
      match e with
      | .modifies_spec _ ⟨_, n⟩ =>
        modifies := modifies ++ [mkIdent n]
      | .requires_spec em ⟨_, l?⟩ ⟨_, free?⟩ cond =>
        reqs := reqs ++ [(← defaultLabel em s!"{pname}_requires" l?, { expr := ← toCoreExpr cond, attr := checkAttrOf free? })]
      | .ensures_spec em ⟨_, l?⟩ ⟨_, free?⟩ cond =>
        enss := enss ++ [(← defaultLabel em s!"{pname}_ensures" l?, { expr := ← toCoreExpr cond, attr := checkAttrOf free? })]
    pure { modifies := modifies, preconditions := reqs, postconditions := enss }

private partial def registerCommandSymbols (cmd : BooleDDM.Command SourceRange) : List (String × Bool) :=
  match cmd with
  | .command_typedecl _ ⟨_, n⟩ _ => [(n, false)]
  | .command_forward_typedecl _ ⟨_, n⟩ _ => [(n, false)]
  | .command_typesynonym _ ⟨_, n⟩ _ _ _ => [(n, false)]
  | .command_constdecl _ ⟨_, n⟩ _ _ => [(n, true)]
  | .command_fndecl _ ⟨_, n⟩ _ _ _ => [(n, true)]
  | .command_fndef _ ⟨_, n⟩ _ _ _ _ _ => [(n, true)]
  | .command_var _ (.bind_mk _ ⟨_, n⟩ _ _) => [(n, false)]
  | .command_procedure _ ⟨_, n⟩ _ _ _ _ _ => [(n, false)]
  | .command_datatype _ ⟨_, n⟩ _ _ => [(n, false)]
  | .command_mutual _ ⟨_, cmds⟩ =>
    (cmds.toList.map registerCommandSymbols).foldl (· ++ ·) []
  | .command_block _ _ => []
  | .command_axiom _ _ _ => []
  | .command_distinct _ _ _ => []

private def initFVars (p : Program) : Array String × Array Bool :=
  match p with
  | .prog _ ⟨_, cmds⟩ =>
    let syms := (cmds.toList.map registerCommandSymbols).foldl (· ++ ·) []
    (syms.map (·.1) |>.toArray, syms.map (·.2) |>.toArray)

private def toCoreDecls (cmd : BooleDDM.Command SourceRange) : TranslateM (List Core.Decl) := do
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
      pure [Core.Decl.proc {
        header := { name := mkIdent n, typeArgs := tys, inputs := inputs, outputs := outputs }
        spec := spec
        body := body
      }]
  | .command_typedecl _ ⟨_, n⟩ ⟨_, args?⟩
  | .command_forward_typedecl _ ⟨_, n⟩ ⟨_, args?⟩ =>
    let numargs := match args? with | none => 0 | some bs => (bindingsToList bs).length
    pure [.type (.con { name := n, numargs := numargs })]
  | .command_typesynonym _ ⟨_, n⟩ ⟨_, args?⟩ _ rhs =>
    let tys := match args? with | none => [] | some bs => (bindingsToList bs).map (fun | .mkBinding _ ⟨_, x⟩ _ => x)
    withTypeBVars tys do
      pure [.type (.syn { name := n, typeArgs := tys, type := ← toCoreMonoType rhs })]
  | .command_constdecl _ ⟨_, n⟩ ⟨_, targs?⟩ ret =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      pure [.func { name := mkIdent n, typeArgs := tys, inputs := [], output := ← toCoreMonoType ret, body := none, concreteEval := none, attr := #[], axioms := [] }]
  | .command_fndecl _ ⟨_, n⟩ ⟨_, targs?⟩ bs ret =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      pure [.func { name := mkIdent n, typeArgs := tys, inputs := ← (bindingsToList bs).mapM toCoreBinding, output := ← toCoreMonoType ret, body := none, concreteEval := none, attr := #[], axioms := [] }]
  | .command_fndef _ ⟨_, n⟩ ⟨_, targs?⟩ bs ret body ⟨_, inline?⟩ =>
    let tys := match targs? with | none => [] | some ts => typeArgsToList ts
    withTypeBVars tys do
      let bsList := bindingsToList bs
      let inputs ← bsList.mapM toCoreBinding
      let inputNames := bsList.map fun
        | .mkBinding _ ⟨_, x⟩ _ => x
      let body ← withBVars inputNames (toCoreExpr body)
      pure [.func { name := mkIdent n, typeArgs := tys, inputs := inputs, output := ← toCoreMonoType ret, body := some body, concreteEval := none, attr := if inline?.isSome then #["inline"] else #[], axioms := [] }]
  | .command_var _ b =>
    let (id, ty) ← toCoreBind b
    let i := (← get).globalVarCounter
    modify fun s => { s with globalVarCounter := i + 1 }
    pure [.var id ty (.fvar () (mkIdent s!"init_{id.name}_{i}") none)]
  | .command_axiom m ⟨_, l?⟩ e =>
    pure [.ax { name := ← defaultLabel m "axiom" l?, e := ← toCoreExpr e }]
  | .command_distinct m ⟨_, l?⟩ ⟨_, es⟩ =>
    pure [.distinct (mkIdent (← defaultLabel m "distinct" l?)) (← es.toList.mapM toCoreExpr)]
  | .command_block _ b =>
    pure [.proc {
      header := { name := mkIdent "", typeArgs := [], inputs := [], outputs := [] }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := ← toCoreBlock b
    }]
  | .command_datatype m ⟨_, dtypeName⟩ ⟨_, typeParams?⟩ ctors =>
    let typeParams := match typeParams? with
      | none => []
      | some bs => (bindingsToList bs).map (fun | .mkBinding _ ⟨_, n⟩ _ => n)
    withTypeBVars typeParams do
      pure [.type (.data [← toCoreDatatype m dtypeName typeParams ctors])]
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
    pure [.type (.data dts)]

def toCoreProgram (p : Program) : Except DiagnosticModel Core.Program := do
  match p with
  | .prog _ ⟨_, cmds⟩ =>
    let (fvars, fvarIsOp) := initFVars p
    let init : TranslateState := { fvars := fvars, fvarIsOp := fvarIsOp }
    let act : TranslateM Core.Program := do
      let decls := (← cmds.toList.mapM toCoreDecls).foldl (· ++ ·) []
      pure { decls := decls }
    act.run' init

open Lean.Parser in

/-- Parse Boole syntax using generated `BooleDDM.Program.ofAst`. -/
def getProgram (p : Strata.Program) : Except DiagnosticModel Program := do
  let cmds : Array (ArgF SourceRange) := p.commands.map ArgF.op
  let progOp : OperationF SourceRange :=
    { ann := default
      name := q`Boole.prog
      args := #[.seq default .spacePrefix cmds] }
  match BooleDDM.Program.ofAst progOp with
  | .ok prog => pure prog
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
